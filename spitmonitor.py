#!/usr/bin/env python2
# -*- coding: utf-8 -*-
##################################################
# GNU Radio Python Flow Graph
# Title: Top Block
# Generated: Tue Jul 16 00:09:34 2019
##################################################

from distutils.version import StrictVersion

if __name__ == '__main__':
    import ctypes
    import sys
    if sys.platform.startswith('linux'):
        try:
            x11 = ctypes.cdll.LoadLibrary('libX11.so')
            x11.XInitThreads()
        except:
            print "Warning: failed to XInitThreads()"

from PyQt5 import Qt
from PyQt5 import Qt, QtCore
from gnuradio import blocks
from gnuradio import eng_notation
from gnuradio import filter
from gnuradio import gr
from gnuradio import qtgui
from gnuradio import zeromq
from gnuradio.eng_option import eng_option
from gnuradio.filter import firdes
from gnuradio.qtgui import Range, RangeWidget
from optparse import OptionParser
import osmosdr
import sip
import sys
import time
from gnuradio import qtgui


import zmq
import array
from collections import deque
import numpy as np
import math
import matplotlib.pyplot as plt
import numpy as numpy
import scipy.signal
import socket
import requests
from scipy import signal
import datetime
import cmath
import json

tau = numpy.pi * 2
max_samples = 1000000
minpktlen = 15 * 8   # Minimum number of bits in a packet
minsamples = 10000   # Minumum number of samples expected
threshold = 0.020    # Threshold over which we consider a signal to have been detected (0.020 is good for +30dBm, 0.005 is good for 0dBm)
symbols_average = 0
invalid_packets = 0
packet_count = 0
debug = True
graph = True
cloud = True
surviveException = False
batt = 0              # Current battery voltage
internal = 0          # Current internal temperature
meat1 = 0             # Current meat thermometer reading (F)
meat2 = 0             # Current meat thermometer reading (F)
meat3 = 0             # Current meat thermometer reading (F)
airtemps = deque('',512)  # Buffer that contains the thermocouple readings (F)
freqSamples = 256     # Number of samples to use for RPM detection
freqAvgSamples = 64   # Number of sets of samples to average for for RPM detection
f1 = 0.020            # Low cutoff frequency for RPM detection
f2 = 0.14             # High cutoff frequency for RPM detection
freqDetectionDelta = 330   # Difference between signal and noise for RPM detection
spp = 32              # Number of samples per period for the longest waveform we can detect for peak detection
setTrackingThreshold = 10   # Threshold over which to start tracking (switch to stdev) for peak detection
clearTrackingThreshold = 5  # Threshold under which to stop tracking (switch from stdev) for peak detection

tracking = False
if graph:
    plt.ion()
fig, (ax1, ax2, ax3) = plt.subplots(3, 1)

def graphit1(data1, data2=[], marker=[]):
    if graph:
        ax1.cla()
        if len(data2) == 0:
            ax1.plot(range(np.alen(data1)), data1)
        else:
            ax1.plot(data1, data2)
        if len(marker) != 0:
            ax1.plot(marker[0], marker[1], marker[2])
        plt.pause(0.01)
    
def graphit2(data1, data2=[], marker=[]):
    if graph:
        ax2.cla()
        if len(data2) == 0:
            ax2.plot(range(np.alen(data1)), data1)
        else:
            ax2.plot(data1, data2)
        if len(marker) != 0:
            ax2.plot(marker[0], marker[1], marker[2])
        plt.pause(0.01)

def graphit3(data1, data2=[], marker=[]):
    if graph:
        ax3.cla()
        if len(data2) == 0:
            ax3.plot(range(np.alen(data1)), data1)
        else:
            ax3.plot(data1, data2)
        if len(marker) != 0:
            ax3.plot(marker[0], marker[1], marker[2])
        plt.pause(0.01)

# Whole packet clock recovery adapted from Michael Ossman's wcpr.py
# To learn more, see the following:
# https://www.youtube.com/watch?v=rQkBDMeODHc
# https://github.com/mossmann/clock-recovery/blob/master/wpcr.py

# determine the clock frequency
# input: magnitude spectrum of clock signal (numpy array)
# output: FFT bin number of clock frequency
def find_clock_frequency(spectrum):
    maxima = scipy.signal.argrelextrema(spectrum, np.greater_equal)[0]
    if len(maxima) == 0:
        return 0
    while maxima[0] < 2:
        maxima = maxima[1:]
    if maxima.any():
        threshold = max(spectrum[2:-1])*0.8
        indices_above_threshold = np.argwhere(spectrum[maxima] > threshold)
        if len(indices_above_threshold) > 0:
            return maxima[indices_above_threshold[0]]
        else:
            return 0
    else:
        return 0

def midpoint(a):
    mean_a = numpy.mean(a)
    mean_a_greater = numpy.ma.masked_greater(a, mean_a)
    high = numpy.ma.median(mean_a_greater)
    mean_a_less_or_equal = numpy.ma.masked_array(a, ~mean_a_greater.mask)
    low = numpy.ma.median(mean_a_less_or_equal)
    return (high + low) / 2

# convert soft symbols into bits (assuming binary symbols)
def slice_bits(symbols):
    global symbols_average
    symbols_average = numpy.average(symbols)
    if debug:
        print "average amplitude: %s" % symbols_average
        print "max amplitude: %s (min threshold: %s)" % (numpy.max(symbols),threshold)
    bits = (symbols >= symbols_average)
    return numpy.array(bits, dtype=numpy.uint8)

# Adapted from: https://stackoverflow.com/questions/28370991/converting-bits-to-bytes-in-python#28371638
def getbytes(bits):
    done = False
    while not done:
        byte = 0
        for _ in range(0, 8):
            try:
                bit = next(bits)
            except StopIteration:
                bit = 0
                done = True
            byte = (byte << 1) | bit
        yield byte

def parsepacket(bits):  
    global invalid_packets, packet_count, meat1, meat2, meat3, internal, batt, airtemps
    packet_count += 1
    bytes = ''
    for b in getbytes(iter(bits)):
        bytes += str(chr(b))
    if len(bits) < minpktlen:
        print "Packet too short (%d bits)" %len(bits)
        invalid_packets += 1
        return False
    syncword = (ord(bytes[0])<<8) + ord(bytes[1])
    if(syncword != 0x2dd4):
        print "Invalid packet"
        invalid_packets += 1
        return False
    length = ord(bytes[2])
    if(length > len(bytes) - 6):
        print "Invalid length"
        invalid_packets += 1
        return False
    crc = (ord(bytes[3+length+1])<<8) + ord(bytes[3+length+2])
    print ":".join("{:02x}".format(ord(bytes[c])) for c in range(4+length+2)),
    print " ",
    for i in range(4+length+2):
        char = bytes[i]
        if ord(char) < 32 or ord(char) >= 127:
            char = '.'
        sys.stdout.write(char)
    print
    batt = socket.ntohs((ord(bytes[7])<<8) + ord(bytes[8])) / 100.0
    print "batt: %s" % (batt)
    internal = socket.ntohs((ord(bytes[9])<<8) + ord(bytes[10])) / 100.0
    print "internal: %s" % (internal)
    meat1 = socket.ntohs((ord(bytes[11])<<8) + ord(bytes[12])) / 100.0
    print "meat1: %s" % (meat1)
    meat2 = socket.ntohs((ord(bytes[13])<<8) + ord(bytes[14])) / 100.0
    print "meat2: %s" % (meat2)
    meat3 = socket.ntohs((ord(bytes[15])<<8) + ord(bytes[16])) / 100.0
    print "meat3: %s" % (meat3)
    airtempfile = open("airtemps.txt", "a")
    sys.stdout.write('airtemp: ')
    for i in range(16):
        airtemp = socket.ntohs((ord(bytes[17+2*i])<<8) + ord(bytes[17+2*i+1])) / 100.0
        airtemps.append(airtemp)
        print airtemp,
        airtempfile.write(str(airtemp)+"\n")
        sys.stdout.write(',')
    sys.stdout.write('\n')
    airtempfile.close()
    return True

def findRotationalFrequency(f):
    # Remove DC bias
    zmean = np.mean(f)
    z = signal.detrend(f, type='constant')
    
    # Average frequency spectra together
    if len(f) < 320:
      return [0,0]
    zmags = []
    mags = []
    n = freqSamples
    for i in range(freqAvgSamples):
        zcomplex = np.fft.rfft(z[-i-n+1:-i-1], len(z[-i-n+1:-i-1]))
        for j in range(len(zcomplex)):
            mags.append(abs(zcomplex[j]))
        zmags.append(mags)
        mags = []
    zmagavg = np.mean(zmags, axis=0)
    zcomplex = []
    for i in range(len(zmagavg)):
        zcomplex.append(cmath.rect(zmagavg[i],0))
    z = np.fft.irfft(zcomplex)
    
    # Apply bandpass filter
    fs = 1360.0 / 914.635294118 # Based on about 15 minutes of sampling with test harness
    numtaps = 146
    filter = signal.firwin(numtaps, [f1,f2], nyq=0.5*fs, pass_zero=False)
    w = signal.lfilter(filter, [1.0], z)
    
    # Calculate FFT
    v = w  			# Rectangular window
    g = np.fft.rfft(v, len(v))
    h = abs(g)
    
    # Find dominant frequency
    #index = np.argmax(h)
    index = find_clock_frequency(h)[0]
    freq = 0
    if index > 1 and index < len(v)-1:
        bin1 = index-1
        bin1f = (index-1) * fs / len(v) # Bin frequency
        bin1a = h[index-1] # Amplitude (weight to apply)
        bin2 = index
        bin2f = (index) * fs / len(v) # Bin frequency
        bin2a = h[index] # Amplitude (weight to apply)
        bin3 = index+1
        bin3f = (index+1) * fs / len(v) # Bin frequency
        bin3a = h[index+1] # Amplitude (weight to apply)
        print "index: ",index
        # Calculate frequency and check if the spit is stopped (frequency amplitude threshold)
        #delta = 330   # Might need to set this lower if the difference in highs and lows is too narrow
        if bin1a > bin3a:
            freq = (bin1a * bin1f + bin2a * bin2f) / (bin1a + bin2a) # Weighted average of frequencies
            if index >= 10:
                avg = np.average(h[index-4:index-1])
                print "bin1a>,>10 bin2a: ",bin2a,"avg + freqDetectionDelta: ",avg+freqDetectionDelta,h[index-4:index-1]
                if bin2a < avg + freqDetectionDelta:
                    freq = 0
                    #print "h[0:30]: ",h[0:30]
            else:
                avg = np.average(h[index+1:index+4])
                print "bin1a>,<10 bin2a: ",bin2a,"avg + freqDetectionDelta: ",avg+freqDetectionDelta,h[index+1:index+4]
                if bin2a < avg + freqDetectionDelta:
                    freq = 0
                    #print "h[0:30]: ",h[0:30]
        else:
            freq = (bin2a * bin2f + bin3a * bin3f) / (bin2a + bin3a) # Weighted average of frequencies
            if index >= 10:
                avg = np.average(h[index-3:index])
                print "bin1a<,>10 bin2a: ",bin2a,"avg + freqDetectionDelta: ",avg+freqDetectionDelta,h[index-3:index]
                if bin2a < avg + freqDetectionDelta:
                    freq = 0
                    #print "h[0:30]: ",h[0:30]
            else:
                avg = np.average(h[index+2:index+5])
                print "bin1a<,<10 bin2a: ",bin2a,"avg + freqDetectionDelta: ",avg+freqDetectionDelta,h[index+2:index+5]
                if bin2a < avg + freqDetectionDelta:
                    freq = 0
                    #print "h[0:30]: ",h[0:30]
        xaxis = np.linspace(0, fs/2.0, len(h), endpoint=False)
        graphit3(xaxis, h, [freq,bin2a,'+'])
    xaxis = np.linspace(0, fs/2.0, len(h), endpoint=False)
    print "Frequency: "+str(freq)

    # Calculate RPM
    rpm = freq * 60
    print "RPM: "+str(rpm)
    return [freq,rpm]

def findFireTemperature(f):
    global tracking

    # Ambient air temperature (Hilbert Transform and amplitude detection)
    g = np.array(f[-128:])
    zmean = np.mean(g)
    print "zmean1: ",zmean
    z = signal.detrend(g, type='constant')
    hilbert = signal.hilbert(z)
    hmagout = abs(hilbert)
    rms = np.sqrt(np.mean(np.square(hmagout)))
    mpeak = (rms + rms * 0.292893219) + zmean
    rms += zmean
    hmagout += zmean
    print "mpeak: ",mpeak
    peak = mpeak
    tpeak = 0
    fstdevhigh = np.mean(f[-spp:]) + 2 * np.std(f[-spp:])
    difference = mpeak - fstdevhigh
    print "Difference: ",difference
    if difference > setTrackingThreshold:
        tracking = True
    if difference < clearTrackingThreshold:
        tracking = False
    if tracking:
        print "Tracking..."
        g = np.array(f[-16:])
        zmean = np.mean(g)
        print "zmean2: ",zmean
        z = signal.detrend(g, type='constant')
        hilbert = signal.hilbert(z)
        hmagout = abs(hilbert)
        trms = np.sqrt(np.mean(np.square(hmagout)))
        print "trms: ",trms
        tpeak = (trms + trms * 0.292893219) + zmean
        print "tpeak: ",tpeak
        trms += zmean
        hmagout += zmean
        peak = tpeak
    print "peak/mpeak/tpeak/fstdevhigh: ",peak,mpeak,tpeak,fstdevhigh
    if tracking:
        graphit2(f[-256:],marker=[[0,256,0,256,0,256],[fstdevhigh,fstdevhigh,mpeak,mpeak,tpeak,tpeak],'+'])
        #graphit3(hmagout, marker=[[0,256,0,256],[peak,peak,tpeak,tpeak],'+'])
    else:
        graphit2(f[-256:],marker=[[0,256,0,256],[peak,peak,fstdevhigh,fstdevhigh],'+'])
        #graphit3(hmagout, marker=[[0,256],[peak,peak],'+'])
    return peak

def processData():
    global tracking,threshold,debug,cloud,surviveException,freqSamples,freqAvgSamples,lowFreq,highFreq
    global freqDetectionDelta,spp,setTrackingThreshold,clearTrackingThreshold

    # Load configuration
    conffile = open('spitmonitor.conf','r')
    config = json.load(conffile)
    threshold = config['threshold']
    debug = config['debug']
    cloud = config['cloud']
    surviveException = config['surviveException']
    freqSamples = config['freqSamples']
    freqAvgSamples = config['freqAvgSamples']
    lowFreq = config['lowFreq']
    highFreq = config['highFreq']
    freqDetectionDelta = config['freqDetectionDelta']
    spp = config['spp']
    setTrackingThreshold = config['setTrackingThreshold']
    clearTrackingThreshold = config['clearTrackingThreshold']
    conffile.close()

    # Perform signal processing on temperature data
    f = np.array(airtemps)
    [freq, rpm] = findRotationalFrequency(f)
    peak = findFireTemperature(f)

    # Log data
    datafile = open("datalog.txt","a")
    datafile.write(str(datetime.datetime.now().strftime('%m/%d/%Y %H:%M:%S')))
    datafile.write(",")
    datafile.write(str(round(peak,2)))
    datafile.write(",")
    datafile.write(str(round(meat1,2)))
    datafile.write(",")
    datafile.write(str(round(meat2,2)))
    datafile.write(",")
    datafile.write(str(round(meat3,2)))
    datafile.write(",")
    datafile.write(str(round(freq,4)))
    datafile.write(",")
    datafile.write(str(round(rpm,2)))
    datafile.write(",")
    datafile.write(str(round(batt,2)))
    datafile.write(",")
    datafile.write(str(round(internal,2)))
    datafile.write(",")
    datafile.write(str(round(symbols_average,3)))
    datafile.write("\n")
    datafile.close()

    # Upload data to the cloud
    if cloud:
        url = "https://api.thingspeak.com/update?apikey=PI7MFD3Z333SSTI6&"
        url += "field1="       # Air temperature
        url += str(round(peak,2))
        url += "&field2="       # Meat1 temperature
        url += str(meat1)
        url += "&field3="       # Battery voltage
        url += str(batt)
        url += "&field4="       # RPM
        url += str(rpm)
        #url += "&field5="       # Not used
        #url += str(numpy.average(list(airtemps)[-16:]))
        url += "&field6="       # Internal temperature
        url += str(internal)
        url += "&field7="       # Meat2 temperature
        url += str(meat2)
        url += "&field8="       # Meat3 temperature
        url += str(meat3)
        print "URL: %s" % (url)
        result = requests.get(url)
        print "Thingspeak: %s" % (result)

def decode(values = []):
    global invalid_packets
    samples = np.array(values)

    # Graph packet
    if graph:
        graphit1(samples)
    
    # Clock Recovery
    b = samples > midpoint(samples)
    d = numpy.diff(b)**2
    f = scipy.fft(d, len(samples))
    p = find_clock_frequency(abs(f))
    p = int(p)
    
    # Symbol extraction
    cycles_per_sample = (p*1.0)/len(f)
    clock_phase = 0.5 + numpy.angle(f[p])/(tau)
    if clock_phase <= 0.5:
        clock_phase += 1
    symbols = []
    for i in range(len(samples)):
        if clock_phase >= 1:
            clock_phase -= 1
            symbols.append(samples[i])
        clock_phase += cycles_per_sample
    if debug:
        print("peak frequency index: %d / %d" % (p, len(f)))
        print("samples per symbol: %f" % (1.0/cycles_per_sample))
        print("clock cycles per sample: %f" % (cycles_per_sample))
        print("clock phase in cycles between 1st and 2nd samples: %f" % (clock_phase))
        print("clock phase in cycles at 1st sample: %f" % (clock_phase - cycles_per_sample/2))
        print("symbol count: %d" % (len(symbols)))
        print("invalid packet count: %d / %d" % (invalid_packets,packet_count))

    # Extract bits
    bits=slice_bits(symbols)
    if debug:
        print(list(bits))

    # Align to sync word for beginning of packet
    for i in range(1,50):
        syncword = [0,0,1,0,1,1,0,1,1,1,0,1,0,1,0,0]
        tmpbits = bits[i:]
        if(cmp(syncword,tmpbits[:16].tolist()) == 0):
            bits = bits[i:]
            break

    # Parse and print packet bytes
    ret = parsepacket(list(bits))

    # Report data to the cloud if the packet was valid
    if ret:
        processData()
    print
    
def zmq_consumer():
    bufsize = 370000            # Number of samples to keep at a time (should be greater than the number of samples in a packet)
    packet_started = False      # Whether or not we've received the first sample of the next/current packet
    packet_finished = False     # Whether or not we have the last sample of the current packet
    packet_samples = 0          # Number of samples in the current packet (once we have them all)
    below_thresh = 0            # Number of samples since we've been below the threshold
    trailing_pad = 6000         # How many samples below the thresold do we want to keep at the end of each packet

    context = zmq.Context()
    results_amplitude = context.socket(zmq.PULL)
    results_amplitude.connect("tcp://127.0.0.1:5558")

    amplitude_ring = deque('',180000)  # Buffer that contains the amplitude samples
    
    while True:
        # Read in the amplitude samples
        raw_amplitude = results_amplitude.recv()
        amp_list = array.array('f', raw_amplitude) # struct.unpack will be faster
        if len(amp_list) >= 0:
            for f in amp_list:
                amplitude_ring.append(f)
                if packet_finished:
                    continue
                if not packet_started:
                    if f > threshold:
                        print("Packet started")
                        packet_started = True
                        # Remove all the samples but the most recent ones (truncate the deque)
                        for i in range(len(amplitude_ring)-200):
                            amplitude_ring.popleft()
                else:
                    if f < threshold:
                        below_thresh += 1
                        if below_thresh >= trailing_pad:
                            multiplier = int(len(amplitude_ring) / 8192);
                            if len(amplitude_ring) == multiplier * 8192:
                                packet_finished = True
                                packet_samples = len(amplitude_ring)
                    else:
                        below_thresh = 0
        
        # Send to demodulator when ready
        if packet_finished:
	    print("Sending samples")
            packet = list(amplitude_ring)
            del packet[packet_samples:]
            decode(packet)
            amplitude_ring.clear()
            packet_started = False
            packet_finished = False
            below_thresh = 0


class top_block(gr.top_block, Qt.QWidget):

    def __init__(self):
        gr.top_block.__init__(self, "Top Block")
        Qt.QWidget.__init__(self)
        self.setWindowTitle("Top Block")
        qtgui.util.check_set_qss()
        try:
            self.setWindowIcon(Qt.QIcon.fromTheme('gnuradio-grc'))
        except:
            pass
        self.top_scroll_layout = Qt.QVBoxLayout()
        self.setLayout(self.top_scroll_layout)
        self.top_scroll = Qt.QScrollArea()
        self.top_scroll.setFrameStyle(Qt.QFrame.NoFrame)
        self.top_scroll_layout.addWidget(self.top_scroll)
        self.top_scroll.setWidgetResizable(True)
        self.top_widget = Qt.QWidget()
        self.top_scroll.setWidget(self.top_widget)
        self.top_layout = Qt.QVBoxLayout(self.top_widget)
        self.top_grid_layout = Qt.QGridLayout()
        self.top_layout.addLayout(self.top_grid_layout)

        self.settings = Qt.QSettings("GNU Radio", "top_block")

        if StrictVersion(Qt.qVersion()) < StrictVersion("5.0.0"):
            self.restoreGeometry(self.settings.value("geometry").toByteArray())
        else:
            self.restoreGeometry(self.settings.value("geometry", type=QtCore.QByteArray))

        ##################################################
        # Variables
        ##################################################
        self.channel_freq = channel_freq = 915003300
        self.samp_rate = samp_rate = 250000
        self.fftsize = fftsize = 512
        self.channel_width = channel_width = 20000
        self.center_freq = center_freq = channel_freq - 50000

        ##################################################
        # Blocks
        ##################################################
        self._channel_width_range = Range(500, 50000, 100, 20000, 200)
        self._channel_width_win = RangeWidget(self._channel_width_range, self.set_channel_width, "channel_width", "counter_slider", float)
        self.top_layout.addWidget(self._channel_width_win)
        self._channel_freq_range = Range(914e6, 916e6, 1000, 915003300, 200)
        self._channel_freq_win = RangeWidget(self._channel_freq_range, self.set_channel_freq, "channel_freq", "counter_slider", float)
        self.top_layout.addWidget(self._channel_freq_win)
        self.zeromq_push_sink_0_0 = zeromq.push_sink(gr.sizeof_float, 1, 'tcp://127.0.0.1:5558', 100, False, -1)
        self.rtlsdr_source_0 = osmosdr.source( args="numchan=" + str(1) + " " + '' )
        self.rtlsdr_source_0.set_sample_rate(samp_rate)
        self.rtlsdr_source_0.set_center_freq(center_freq, 0)
        self.rtlsdr_source_0.set_freq_corr(0, 0)
        self.rtlsdr_source_0.set_dc_offset_mode(0, 0)
        self.rtlsdr_source_0.set_iq_balance_mode(0, 0)
        self.rtlsdr_source_0.set_gain_mode(False, 0)
        self.rtlsdr_source_0.set_gain(30, 0)
        self.rtlsdr_source_0.set_if_gain(20, 0)
        self.rtlsdr_source_0.set_bb_gain(20, 0)
        self.rtlsdr_source_0.set_antenna('', 0)
        self.rtlsdr_source_0.set_bandwidth(0, 0)

        self.qtgui_waterfall_sink_x_0_1 = qtgui.waterfall_sink_c(
        	fftsize, #size
        	firdes.WIN_BLACKMAN_hARRIS, #wintype
        	center_freq, #fc
        	samp_rate, #bw
        	"Post-filter", #name
                1 #number of inputs
        )
        self.qtgui_waterfall_sink_x_0_1.set_update_time(0.10)
        self.qtgui_waterfall_sink_x_0_1.enable_grid(False)
        self.qtgui_waterfall_sink_x_0_1.enable_axis_labels(True)

        if not True:
          self.qtgui_waterfall_sink_x_0_1.disable_legend()

        if "complex" == "float" or "complex" == "msg_float":
          self.qtgui_waterfall_sink_x_0_1.set_plot_pos_half(not True)

        labels = ['', '', '', '', '',
                  '', '', '', '', '']
        colors = [0, 0, 0, 0, 0,
                  0, 0, 0, 0, 0]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
                  1.0, 1.0, 1.0, 1.0, 1.0]
        for i in xrange(1):
            if len(labels[i]) == 0:
                self.qtgui_waterfall_sink_x_0_1.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_waterfall_sink_x_0_1.set_line_label(i, labels[i])
            self.qtgui_waterfall_sink_x_0_1.set_color_map(i, colors[i])
            self.qtgui_waterfall_sink_x_0_1.set_line_alpha(i, alphas[i])

        self.qtgui_waterfall_sink_x_0_1.set_intensity_range(-140, 10)

        self._qtgui_waterfall_sink_x_0_1_win = sip.wrapinstance(self.qtgui_waterfall_sink_x_0_1.pyqwidget(), Qt.QWidget)
        self.top_layout.addWidget(self._qtgui_waterfall_sink_x_0_1_win)
        self.qtgui_waterfall_sink_x_0 = qtgui.waterfall_sink_c(
        	fftsize, #size
        	firdes.WIN_BLACKMAN_hARRIS, #wintype
        	center_freq, #fc
        	samp_rate, #bw
        	"Raw samples", #name
                1 #number of inputs
        )
        self.qtgui_waterfall_sink_x_0.set_update_time(0.10)
        self.qtgui_waterfall_sink_x_0.enable_grid(False)
        self.qtgui_waterfall_sink_x_0.enable_axis_labels(True)

        if not True:
          self.qtgui_waterfall_sink_x_0.disable_legend()

        if "complex" == "float" or "complex" == "msg_float":
          self.qtgui_waterfall_sink_x_0.set_plot_pos_half(not True)

        labels = ['', '', '', '', '',
                  '', '', '', '', '']
        colors = [0, 0, 0, 0, 0,
                  0, 0, 0, 0, 0]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
                  1.0, 1.0, 1.0, 1.0, 1.0]
        for i in xrange(1):
            if len(labels[i]) == 0:
                self.qtgui_waterfall_sink_x_0.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_waterfall_sink_x_0.set_line_label(i, labels[i])
            self.qtgui_waterfall_sink_x_0.set_color_map(i, colors[i])
            self.qtgui_waterfall_sink_x_0.set_line_alpha(i, alphas[i])

        self.qtgui_waterfall_sink_x_0.set_intensity_range(-140, 10)

        self._qtgui_waterfall_sink_x_0_win = sip.wrapinstance(self.qtgui_waterfall_sink_x_0.pyqwidget(), Qt.QWidget)
        self.top_layout.addWidget(self._qtgui_waterfall_sink_x_0_win)
        self.qtgui_time_sink_x_0_1_0 = qtgui.time_sink_f(
        	fftsize, #size
        	samp_rate, #samp_rate
        	"Magnitude", #name
        	1 #number of inputs
        )
        self.qtgui_time_sink_x_0_1_0.set_update_time(0.10)
        self.qtgui_time_sink_x_0_1_0.set_y_axis(0, 0.4)

        self.qtgui_time_sink_x_0_1_0.set_y_label('Amplitude', "")

        self.qtgui_time_sink_x_0_1_0.enable_tags(-1, True)
        self.qtgui_time_sink_x_0_1_0.set_trigger_mode(qtgui.TRIG_MODE_AUTO, qtgui.TRIG_SLOPE_POS, 0.018, 0, 0, "")
        self.qtgui_time_sink_x_0_1_0.enable_autoscale(False)
        self.qtgui_time_sink_x_0_1_0.enable_grid(False)
        self.qtgui_time_sink_x_0_1_0.enable_axis_labels(True)
        self.qtgui_time_sink_x_0_1_0.enable_control_panel(True)
        self.qtgui_time_sink_x_0_1_0.enable_stem_plot(False)

        if not True:
          self.qtgui_time_sink_x_0_1_0.disable_legend()

        labels = ['', '', '', '', '',
                  '', '', '', '', '']
        widths = [1, 1, 1, 1, 1,
                  1, 1, 1, 1, 1]
        colors = ["blue", "red", "green", "black", "cyan",
                  "magenta", "yellow", "dark red", "dark green", "blue"]
        styles = [1, 1, 1, 1, 1,
                  1, 1, 1, 1, 1]
        markers = [-1, -1, -1, -1, -1,
                   -1, -1, -1, -1, -1]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
                  1.0, 1.0, 1.0, 1.0, 1.0]

        for i in xrange(1):
            if len(labels[i]) == 0:
                self.qtgui_time_sink_x_0_1_0.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_time_sink_x_0_1_0.set_line_label(i, labels[i])
            self.qtgui_time_sink_x_0_1_0.set_line_width(i, widths[i])
            self.qtgui_time_sink_x_0_1_0.set_line_color(i, colors[i])
            self.qtgui_time_sink_x_0_1_0.set_line_style(i, styles[i])
            self.qtgui_time_sink_x_0_1_0.set_line_marker(i, markers[i])
            self.qtgui_time_sink_x_0_1_0.set_line_alpha(i, alphas[i])

        self._qtgui_time_sink_x_0_1_0_win = sip.wrapinstance(self.qtgui_time_sink_x_0_1_0.pyqwidget(), Qt.QWidget)
        self.top_layout.addWidget(self._qtgui_time_sink_x_0_1_0_win)
        self.blocks_complex_to_mag_0 = blocks.complex_to_mag(1)
        self.band_pass_filter_0 = filter.fir_filter_ccc(1, firdes.complex_band_pass(
        	1, samp_rate, channel_freq - center_freq - channel_width/2, channel_freq - center_freq + channel_width/2, 1000, firdes.WIN_HAMMING, 6.76))

        ##################################################
        # Connections
        ##################################################
        self.connect((self.band_pass_filter_0, 0), (self.blocks_complex_to_mag_0, 0))
        self.connect((self.band_pass_filter_0, 0), (self.qtgui_waterfall_sink_x_0_1, 0))
        self.connect((self.blocks_complex_to_mag_0, 0), (self.qtgui_time_sink_x_0_1_0, 0))
        self.connect((self.blocks_complex_to_mag_0, 0), (self.zeromq_push_sink_0_0, 0))
        self.connect((self.rtlsdr_source_0, 0), (self.band_pass_filter_0, 0))
        self.connect((self.rtlsdr_source_0, 0), (self.qtgui_waterfall_sink_x_0, 0))

    def closeEvent(self, event):
        self.settings = Qt.QSettings("GNU Radio", "top_block")
        self.settings.setValue("geometry", self.saveGeometry())
        event.accept()

    def get_channel_freq(self):
        return self.channel_freq

    def set_channel_freq(self, channel_freq):
        self.channel_freq = channel_freq
        self.set_center_freq(self.channel_freq - 50000)
        self.band_pass_filter_0.set_taps(firdes.complex_band_pass(1, self.samp_rate, self.channel_freq - self.center_freq - self.channel_width/2, self.channel_freq - self.center_freq + self.channel_width/2, 1000, firdes.WIN_HAMMING, 6.76))

    def get_samp_rate(self):
        return self.samp_rate

    def set_samp_rate(self, samp_rate):
        self.samp_rate = samp_rate
        self.rtlsdr_source_0.set_sample_rate(self.samp_rate)
        self.qtgui_waterfall_sink_x_0_1.set_frequency_range(self.center_freq, self.samp_rate)
        self.qtgui_waterfall_sink_x_0.set_frequency_range(self.center_freq, self.samp_rate)
        self.qtgui_time_sink_x_0_1_0.set_samp_rate(self.samp_rate)
        self.band_pass_filter_0.set_taps(firdes.complex_band_pass(1, self.samp_rate, self.channel_freq - self.center_freq - self.channel_width/2, self.channel_freq - self.center_freq + self.channel_width/2, 1000, firdes.WIN_HAMMING, 6.76))

    def get_fftsize(self):
        return self.fftsize

    def set_fftsize(self, fftsize):
        self.fftsize = fftsize

    def get_channel_width(self):
        return self.channel_width

    def set_channel_width(self, channel_width):
        self.channel_width = channel_width
        self.band_pass_filter_0.set_taps(firdes.complex_band_pass(1, self.samp_rate, self.channel_freq - self.center_freq - self.channel_width/2, self.channel_freq - self.center_freq + self.channel_width/2, 1000, firdes.WIN_HAMMING, 6.76))

    def get_center_freq(self):
        return self.center_freq

    def set_center_freq(self, center_freq):
        self.center_freq = center_freq
        self.rtlsdr_source_0.set_center_freq(self.center_freq, 0)
        self.qtgui_waterfall_sink_x_0_1.set_frequency_range(self.center_freq, self.samp_rate)
        self.qtgui_waterfall_sink_x_0.set_frequency_range(self.center_freq, self.samp_rate)
        self.band_pass_filter_0.set_taps(firdes.complex_band_pass(1, self.samp_rate, self.channel_freq - self.center_freq - self.channel_width/2, self.channel_freq - self.center_freq + self.channel_width/2, 1000, firdes.WIN_HAMMING, 6.76))


def main(top_block_cls=top_block, options=None):

    if StrictVersion("4.5.0") <= StrictVersion(Qt.qVersion()) < StrictVersion("5.0.0"):
        style = gr.prefs().get_string('qtgui', 'style', 'raster')
        Qt.QApplication.setGraphicsSystem(style)
    qapp = Qt.QApplication(sys.argv)

    tb = top_block_cls()
    tb.start()
    #tb.show()

    while True:
        try:
            zmq_consumer()
        except Exception as e:
            print "Caught exception:"
            print e
        if not surviveException:
            raise

    def quitting():
        tb.stop()
        tb.wait()
    qapp.aboutToQuit.connect(quitting)
    qapp.exec_()


if __name__ == '__main__':
    main()

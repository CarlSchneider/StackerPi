#!/usr/bin/env python2
# StackerPi macro focus stacker controller for Raspberry Pi by Carl Schneider
# This must run as root (sudo python StackerPi.py) due to WiringPi2, etc.
#
# http://www.adafruit.com/products/998  (Raspberry Pi Model B)
# http://www.adafruit.com/products/1601 (PiTFT Mini Kit)
#
# Prerequisite tutorials: aside from the basic Raspbian setup and PiTFT setup
# http://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi
#
# StackerPi is based on code borrowed from the following Makers, with my sincere thanks
# because without it I would still be tryin to figure out how to be Pythonic :),
# David Hunt's (dave@davidhunt.ie) lapse.py which in turn was
# based on cam.py by Phil Burgess / Paint Your Dragon for Adafruit Industries.
# A4988 micorstep size setting code borrowed from Focus Stacking mit dem Raspberry Pi from
# Stefan at musicdiver.com. Ich sprechen nicht Duits! Dankescheun Stefan.
# BSD license, all text above must be included in any redistribution.

import wiringpi2
import atexit
import cPickle as pickle
import errno
import fnmatch
import io
import os
import pygame
import threading
import signal
import sys

from pygame.locals import *
from subprocess import call  
from time import sleep
from datetime import datetime, timedelta

# UI classes ---------------------------------------------------------------

# Icon is a very simple bitmap class, just associates a name and a pygame
# image (PNG loaded from icons directory) for each.
# There isn't a globally-declared fixed list of Icons.  Instead, the list
# is populated at runtime from the contents of the 'icons' directory.

class Icon:

	def __init__(self, name):
	  self.name = name
	  try:
	    self.bitmap = pygame.image.load(iconPath + '/' + name + '.png')
	  except:
	    pass

# Button is a simple tappable screen region.  Each has:
#  - bounding rect ((X,Y,W,H) in pixels)
#  - optional background color and/or Icon (or None), always centered
#  - optional foreground Icon, always centered
#  - optional single callback function
#  - optional single value passed to callback
# Occasionally Buttons are used as a convenience for positioning Icons
# but the taps are ignored.  Stacking order is important; when Buttons
# overlap, lowest/first Button in list takes precedence when processing
# input, and highest/last Button is drawn atop prior Button(s).  This is
# used, for example, to center an Icon by creating a passive Button the
# width of the full screen, but with other buttons left or right that
# may take input precedence (e.g. the Effect labels & buttons).
# After Icons are loaded at runtime, a pass is made through the global
# buttons[] list to assign the Icon objects (from names) to each Button.

class Button:

	def __init__(self, rect, **kwargs):
	  self.rect     = rect # Bounds
	  self.color    = None # Background fill color, if any
	  self.iconBg   = None # Background Icon (atop color fill)
	  self.iconFg   = None # Foreground Icon (atop background)
	  self.bg       = None # Background Icon name
	  self.fg       = None # Foreground Icon name
	  self.callback = None # Callback function
	  self.value    = None # Value passed to callback
	  self.butdown = None # boolean to reset iconFg to iconBg
	  for key, value in kwargs.iteritems():
	    if   key == 'color': self.color    = value
	    elif key == 'bg'   : self.bg       = value
	    elif key == 'fg'   : self.fg       = value
	    elif key == 'cb'   : self.callback = value
	    elif key == 'value': self.value    = value

	def selected(self, pos):
	  self.butdown = False
	  x1 = self.rect[0]
	  y1 = self.rect[1]
	  x2 = x1 + self.rect[2] - 1
	  y2 = y1 + self.rect[3] - 1
	  if ((pos[0] >= x1) and (pos[0] <= x2) and
	      (pos[1] >= y1) and (pos[1] <= y2)):
	    self.butdown = True
	    if self.callback:
	      if self.value is None: self.callback()
	      else:                  self.callback(self.value)
	    return True
	  return False

	def draw(self, screen):
	  if self.color:
	    screen.fill(self.color, self.rect)
	  if self.iconBg:
	    screen.blit(self.iconBg.bitmap,
	      (self.rect[0]+(self.rect[2]-self.iconBg.bitmap.get_width())/2,
	       self.rect[1]+(self.rect[3]-self.iconBg.bitmap.get_height())/2))
	  if self.iconFg and self.butdown:
	    self.butdown == False
	    screen.blit(self.iconFg.bitmap,
	      (self.rect[0]+(self.rect[2]-self.iconFg.bitmap.get_width())/2,
	       self.rect[1]+(self.rect[3]-self.iconFg.bitmap.get_height())/2))

# UI callbacks -------------------------------------------------------------
# These are defined before globals because they're referenced by items in
# the global buttons[] list.
#
# This module determines the micro-stepping and macro steps required for
# the Canon MPE-65E lens DoF slice based on f-stop and magnification

def stepCallback(n):
    global screenMode
    global stepsize
    global macrostep
    global depressed
    global depmem
    
    depmem = depressed
    depressed = n
    
    if n == -1:
	screenMode = 1 #returnScreen
    elif n in (1, 17, 23, 29):
	stepsize = 1
	macrostep = 4
    elif n in (2, 3, 8, 9, 14, 15, 20):
	stepsize = 1
	macrostep = 1
    elif n in (4, 5, 10):
	stepsize = 2
	macrostep = 1
    elif n in (6, 22):
	stepsize = 1
	macrostep = 6
    elif n in (7, 13, 18, 19, 24, 25):
	stepsize = 1
	macrostep = 2
    elif n in (11, 27):
	stepsize = 1
	macrostep = 9
    elif n in (12, 30):
	stepsize = 1
	macrostep = 3
    elif n == 16:
	stepsize = 1
	macrostep = 12
    elif n == 17:
	stepsize = 1
	macrostep = 4
    elif n == 21:
	stepsize = 1
	macrostep = 18
    elif n == 26:
	stepsize = 1
	macrostep = 25
    elif n == 28:
	stepsize = 1
	macrostep = 5
    elif n == 30:
	stepsize = 1
	macrostep = 3
#	
# This module sets the microstep size on the A4988 stepper motor driver
#
def setStepSize(stepsize):
    if stepsize == 1:
        gpio.digitalWrite(MS1Pin, int(microStepSizeBits[0][0:1]))
        gpio.digitalWrite(MS2Pin, int(microStepSizeBits[0][1:2]))
        gpio.digitalWrite(MS3Pin, int(microStepSizeBits[0][2:3]))
    elif stepsize == 2:
        gpio.digitalWrite(MS1Pin, int(microStepSizeBits[1][0:1]))
        gpio.digitalWrite(MS2Pin, int(microStepSizeBits[1][1:2]))
        gpio.digitalWrite(MS3Pin, int(microStepSizeBits[1][2:3]))
    elif stepsize == 4:
        gpio.digitalWrite(MS1Pin, int(microStepSizeBits[2][0:1]))
        gpio.digitalWrite(MS2Pin, int(microStepSizeBits[2][1:2]))
        gpio.digitalWrite(MS3Pin, int(microStepSizeBits[2][2:3]))
    elif stepsize == 8:
        gpio.digitalWrite(MS1Pin, int(microStepSizeBits[3][0:1]))
        gpio.digitalWrite(MS2Pin, int(microStepSizeBits[3][1:2]))
        gpio.digitalWrite(MS3Pin, int(microStepSizeBits[3][2:3]))
    elif stepsize == 16:
        gpio.digitalWrite(MS1Pin, int(microStepSizeBits[4][0:1]))
        gpio.digitalWrite(MS2Pin, int(microStepSizeBits[4][1:2]))
        gpio.digitalWrite(MS3Pin, int(microStepSizeBits[4][2:3]))

def motorCallback(n): # Pass 1 (next setting) or -1 (prev setting)
	global screenMode
	global motorRunning
	global motorDirection
	global motorpin
	global motorpinA
	
	if n == 1: #motor direction left 
		gpio.digitalWrite(motorDirection, False) #set stepper motor direction forward
		gpio.digitalWrite(motorpinA, True)
		pygame.time.wait(2) # force pause in ms between steps of stepper motor
		gpio.digitalWrite(motorpinA, False)

	elif n == 2: #motor direction right 
		gpio.digitalWrite(motorDirection, True) #set stepper motor direction backward
		gpio.digitalWrite(motorpinA, True)
		pygame.time.wait(2) # force pause in ms between steps of stepper motor
		gpio.digitalWrite(motorpinA, False)

	elif n == 3: #bigstep left
	  for i in range(100):
		gpio.digitalWrite(motorDirection, False) #set stepper motor direction forward
		gpio.digitalWrite(motorpinA, True)
		pygame.time.wait(2) # force pause in ms between steps of stepper motor
		gpio.digitalWrite(motorpinA, False)
		i += 1
		
	elif n == 4: #bigstep right
	  for i in range(100):
		gpio.digitalWrite(motorDirection, True) #set stepper motor direction forward
		gpio.digitalWrite(motorpinA, True)
		pygame.time.wait(2) # force pause in ms between steps of stepper motor
		gpio.digitalWrite(motorpinA, False)
		i +=1

def numericCallback(n): # Pass 1 (next setting) or -1 (prev setting)
	global screenMode
	global numberstring
	global numeric
	global dict_idx
	if n < 10:
		numberstring = numberstring + str(n)
	elif n == 10:
		numberstring = numberstring[:-1]
	elif n == 11:
		screenMode = 1
	elif n == 12:
		screenMode = 1 #returnScreen
		numeric = int(numberstring)
		v[dict_idx] = numeric

def settingCallback(n): # Pass 1 (next setting) or -1 (prev setting)
	global screenMode
	screenMode += n
	if screenMode < 1:               screenMode = len(buttons) - 1
	elif screenMode >= len(buttons): screenMode = 1

def valuesCallback(n): # Pass 1 (next setting) or -1 (prev setting)
	global screenMode
	global returnScreen
	global numberstring
	global numeric
	global v
	global dict_idx
	global stepsize
	global distance

	if n == -1:
		screenMode = 0
		saveSettings()
	if n == 1:
		dict_idx='Pulse'
		numberstring = str(v[dict_idx])
		stepsize = v[dict_idx] # added stepsize should be 1,2,4,8,16
		setStepSize(stepsize)
		screenMode = 3 #changed from 2 to 3
		returnScreen = 1
	elif n == 2:
		dict_idx='Interval'
		numberstring = str(v[dict_idx])
		distance = float(v['Interval'])/1000.0
		setStepSize(stepsize)
		print("bigstep, distance", bigstep, distance)
		screenMode = 2
		returnScreen = 1
	elif n == 3:
		dict_idx='Images'
		numberstring = str(v[dict_idx])
		screenMode = 2
		returnScreen = 1

def viewCallback(n): # Viewfinder buttons
	global screenMode, screenModePrior
	if n is 0:   # Gear icon
	  screenMode = 1

def doneCallback(): # Exit settings
	global screenMode
	if screenMode > 0:
	  saveSettings()
	screenMode = 0 # Switch back to main window

def startCallback(n): # start/Stop the timelapse thread
	global t, busy, threadExited
	global currentframe, memframe
	if n == 1: 
		if busy == False:
			if (threadExited == True):
				# Re-instanciate the object for the next start
				t = threading.Thread(target=timeLapse)
				threadExited = False
			t.start()
	if n == 0:
		if busy == True:
			busy = False
			t.join()
			memframe = currentframe
			currentframe = 0
			# Re-instanciate the object for the next time around.
			t = threading.Thread(target=timeLapse)
	
	if n == 2:
	    for i in range(1 , ((v['Images']) * macrostep) + 1):
		    gpio.digitalWrite(motorDirection, True) #set stepper motor direction reverse
		    gpio.digitalWrite(motorpinA, True)
		    pygame.time.wait(2) # force pause in ms between steps of stepper motor
		    gpio.digitalWrite(motorpinA, False)

def timeLapse():
	global v
	global settling_time
	global shutter_length
	global motorpin
	global shutterpin
	global backlightpin
	global busy, threadExited
	global currentframe
	global stepsize
	global macrostep
	global breakframe
	global distance # define distance which is step*stepsize

	busy = True

	for i in range( 1 , v['Images'] + 1 ):
		if busy == False:
			breakframe = currentframe
			break
		currentframe = i
		gpio.digitalWrite(motorDirection, False) #set stepper motor direction forward
		for j in range (1, macrostep + 1):
		    gpio.digitalWrite(motorpinA, True)
		    pygame.time.wait(10) # force pause in ms between steps of stepper motor
		    gpio.digitalWrite(motorpinA, False)

		sleep(settling_time)

		# disable the backlight, critical for night timelapses, also saves power
		#os.system("echo '0' > /sys/class/gpio/gpio252/value") # not using the HAT
		
		gpio.digitalWrite(shutterpin,gpio.HIGH)
		sleep(shutter_length + pause)
		gpio.digitalWrite(shutterpin,gpio.LOW)
		
		#  enable the backlight
		#os.system("echo '1' > /sys/class/gpio/gpio252/value") # not using the HAT
#
# Rewind camera to start position only if Stopped before completion
#
	if busy == False:
	    for i in range(1 , ((v['Images']-breakframe) * macrostep) + 1):
		    gpio.digitalWrite(motorDirection, True) #set stepper motor direction reverse
		    gpio.digitalWrite(motorpinA, True)
		    pygame.time.wait(2) # force pause in ms between steps of stepper motor
		    gpio.digitalWrite(motorpinA, False)
		
	currentframe = 0
	busy = False
	threadExited = True


def signal_handler(signal, frame):
	print ("got SIGTERM")
	pygame.quit()
	sys.exit()

#
# Global stuff -------------------------------------------------------------

t = threading.Thread(target=timeLapse)
busy            = False
threadExited    = False
screenMode      =  0      # Current screen mode; default = viewfinder
screenModePrior = -1      # Prior screen mode (for detecting changes)
iconPath        = 'icons' # Subdirectory containing UI bitmaps (PNG format)
numeric         = 0       # number from numeric keypad      
numberstring	= "0"
motorRunning	= 0	# Not used
motorDirection	= 18	#changed to pin for driver direction
returnScreen   = 0
shutterpin     = 17
motorpinA      = 27 	# Used as A4988 step pin driver
#backlightpin   = 252 #no touch screen connected
distance = 1.0
stepsize = 1
macrostep = 1
bigstep = 1
currentframe   = 0
framecount     = 20
settling_time  = 3.0	# delay to let everything come to rest
shutter_length = 1.0/60	# using a Canon M-14E flash
pause = 0.5		# Hold shutter trigger on to ensure shutter release
MS1Pin = 23
MS2Pin = 24
MS3Pin = 25
microStepSizeBits = ['000', '100', '010', '110', '111']
butdown = pygame.image.load("icons/bdt.png")
butup    = pygame.image.load("icons/but.png")
depressed = 0
breakframe = 0
depmem = 0
memframe = 0
dict_idx	   = "Interval"
#
# Pulse is StepSize which is the linear distance per step 90mm/0.45/5.18; where
# the linear actuator Fest DGE-25-400-ZR is a toothed timing belt based unit.
# One rotation of the drive gear results in a linear motion of the timing belt
# of 90mm. On a 200 step stepper motor this results in a 0.045mm linear movement.
# However the stepper motor has a 1:5.18 planetary reduction gearbox attached.
# This arrangement of stepper, reducion gearbox and linear actuator, with microstepping
# yields the required minute linear increments of the camera platform to achieve the
# steps required at f2.8 and 5X on the lens, which is a DoF of 0.048mm through to f16 at 1X
# with a Dof of 2.24mm
#
v = { "Pulse": 86.725868726,
	"Interval": 3000,
	"Images": 150}

icons = [] # This list gets populated at startup

# buttons[] is a list of lists; each top-level list element corresponds
# to one screen mode (e.g. viewfinder, image playback, storage settings),
# and each element within those lists corresponds to one UI button.
# There's a little bit of repetition (e.g. prev/next buttons are
# declared for each settings screen, rather than a single reusable
# set); trying to reuse those few elements just made for an ugly
# tangle of code elsewhere.

buttons = [

  # Screen mode 0 is main view screen of current status
  [Button((  0,180,100, 60), bg='start', cb=startCallback, value=1),
   Button((100,180, 60, 60), bg='cog',   cb=viewCallback, value=0),
   Button((160,180,100, 60), bg='stop',  cb=startCallback, value=0),
   Button((260,180, 60, 60), bg='rewind', cb=startCallback, value = 2)],

  # Screen 1 for changing values and setting motor direction
  [Button((260,  0, 60, 60), bg='cog',   cb=valuesCallback, value=1),
   Button((260, 60, 60, 60)),
   Button((260,120, 60, 60), bg='cog',   cb=valuesCallback, value=3),
   Button((  0,180,80, 60), bg='oksmall',    cb=valuesCallback, value=-1),
   Button((140,180, 70, 60), bg='left',  cb=motorCallback, value=2),
   Button((80,180, 70, 60), bg='bigleft',  cb=motorCallback, value=4),
   Button((200,180, 70, 60), bg='right', cb=motorCallback, value=1),
   Button((260,180, 70, 60), bg='bigright',  cb=motorCallback, value=3)],

  # Screen 2 for numeric input
  [Button((  0,  0,320, 60), bg='box'),
   Button((180,120, 60, 60), bg='0',     cb=numericCallback, value=0),
   Button((  0,180, 60, 60), bg='1',     cb=numericCallback, value=1),
   Button((120,180, 60, 60), bg='3',     cb=numericCallback, value=3),
   Button(( 60,180, 60, 60), bg='2',     cb=numericCallback, value=2),
   Button((  0,120, 60, 60), bg='4',     cb=numericCallback, value=4),
   Button(( 60,120, 60, 60), bg='5',     cb=numericCallback, value=5),
   Button((120,120, 60, 60), bg='6',     cb=numericCallback, value=6),
   Button((  0, 60, 60, 60), bg='7',     cb=numericCallback, value=7),
   Button(( 60, 60, 60, 60), bg='8',     cb=numericCallback, value=8),
   Button((120, 60, 60, 60), bg='9',     cb=numericCallback, value=9),
   Button((240,120, 80, 60), bg='del',   cb=numericCallback, value=10),
   Button((180,180,140, 60), bg='ok',    cb=numericCallback, value=12),
   Button((180, 60,140, 60), bg='cancel',cb=numericCallback, value=11)],
   
   # Screen 3 for DoF slice input
   [Button((0,0,45,40), bg='OK3', cb=stepCallback, value=-1),
   Button((0,40,45,40), bg='1x'),
   Button((0,80,45,40), bg='2x'),
   Button((0,120,45,40), bg='3x'),
   Button((0,160,45,40), bg='4x'),
   Button((0,200,45,40), bg='5x'),
   Button((45,0,45,40), bg='f2'),
   Button((45,40,45,40), bg='but', fg='bdt', cb=stepCallback, value=1),
   Button((45,80,45,40),bg='but', fg='bdt',cb=stepCallback, value=2),
   Button((45,120,45,40), bg='but', fg='bdt',cb=stepCallback, value=3),
   Button((45,160,45,40), bg='but', fg='bdt',cb=stepCallback, value=4),
   Button((45,200,45,40), bg='but', fg='bdt',cb=stepCallback, value=5),
   Button((90,0,45,40), bg='f4'),
   Button((90,40,45,40), bg='but', fg='bdt',cb=stepCallback, value=6),
   Button((90,80,45,40), bg='but', fg='bdt',cb=stepCallback, value=7),
   Button((90,120,45,40), bg='but', fg='bdt',cb=stepCallback, value=8),
   Button((90,160,45,40), bg='but', fg='bdt',cb=stepCallback, value=9),
   Button((90,200,45,40), bg='but', fg='bdt',cb=stepCallback, value=10),
   Button((135,0,45,40), bg='f5'),
   Button((135,40,45,40), bg='but', fg='bdt',cb=stepCallback, value=11),
   Button((135,80,45,40), bg='but', fg='bdt',cb=stepCallback, value=12),
   Button((135,120,45,40), bg='but', fg='bdt',cb=stepCallback, value=13),
   Button((135,160,45,40), bg='but', fg='bdt',cb=stepCallback, value=14),
   Button((135,200,45,40), bg='but', fg='bdt',cb=stepCallback, value=15),
   Button((180,0,45,40), bg='f8'),
   Button((180,40,45,40), bg='but', fg='bdt',cb=stepCallback, value=16),
   Button((180,80,45,40), bg='but', fg='bdt',cb=stepCallback, value=17),
   Button((180,120,45,40), bg='but', fg='bdt',cb=stepCallback, value=18),
   Button((180,160,45,40), bg='but', fg='bdt',cb=stepCallback, value=19),
   Button((180,200,45,40), bg='but', fg='bdt',cb=stepCallback, value=20),
   Button((225,0,45,40), bg='f11'),
   Button((225,40,45,40), bg='but', fg='bdt',cb=stepCallback, value=21),
   Button((225,80,45,40), bg='but', fg='bdt',cb=stepCallback, value=22),
   Button((225,120,45,40), bg='but', fg='bdt',cb=stepCallback, value=23),
   Button((225,160,45,40), bg='but', fg='bdt',cb=stepCallback, value=24),
   Button((225,200,45,40), bg='but', fg='bdt',cb=stepCallback, value=25),
   Button((270,0,45,40), bg='f16'),
   Button((270,40,45,40), bg='but', fg='bdt',cb=stepCallback, value=26),
   Button((270,80,45,40), bg='but', fg='bdt',cb=stepCallback, value=27),
   Button((270,120,45,40), bg='but', fg='bdt',cb=stepCallback, value=28),
   Button((270,160,45,40), bg='but', fg='bdt',cb=stepCallback, value=29),
   Button((270,200,45,40), bg='but', fg='bdt',cb=stepCallback, value=30)]
]


# Assorted utility functions -----------------------------------------------


def saveSettings():
	global v
	try:
	  outfile = open('lapse.pkl', 'wb')
	  # Use a dictionary (rather than pickling 'raw' values) so
	  # the number & order of things can change without breaking.
	  pickle.dump(v, outfile)
	  outfile.close()
	except:
	  pass

def loadSettings():
	global v
	try:
	  infile = open('lapse.pkl', 'rb')
	  v = pickle.load(infile)
	  infile.close()
	except:
	  pass



# Initialization -----------------------------------------------------------

# Init framebuffer/touchscreen environment variables # not using the HAT
#os.putenv('SDL_VIDEODRIVER', 'fbcon') # not using the HAT
#os.putenv('SDL_FBDEV'      , '/dev/fb1') # not using the HAT
#os.putenv('SDL_MOUSEDRV'   , 'TSLIB') # not using the HAT
#os.putenv('SDL_MOUSEDEV'   , '/dev/input/touchscreen') # not using the HAT


# Init pygame and screen
print ("Initting...")
pygame.init()
pygame.key.set_repeat(100,10)
print ("Setting Mouse invisible...")
pygame.mouse.set_visible(True) # set True to drive this on screen
print ("Setting fullscreen...")
# modes = pygame.display.list_modes(16) # removed to hard code screen size
# screen = pygame.display.set_mode(modes[0], FULLSCREEN, 16) # as a floating window
screen = pygame.display.set_mode((320,240)) # hard coded screen size
pygame.display.set_caption("Macro Stacker") # added window caption
print ("Loading Icons...")
# Load all icons at startup.
for file in os.listdir(iconPath):
  if fnmatch.fnmatch(file, '*.png'):
    icons.append(Icon(file.split('.')[0]))
# Assign Icons to Buttons, now that they're loaded
print("Assigning Buttons")
for s in buttons:        # For each screenful of buttons...
  for b in s:            #  For each button on screen...
    for i in icons:      #   For each icon...
      if b.bg == i.name: #    Compare names; match?
        b.iconBg = i     #     Assign Icon to Button
        b.bg     = None  #     Name no longer used; allow garbage collection
      if b.fg == i.name:
        b.iconFg = i
        b.fg     = None

# Set up GPIO pins
print ("Init GPIO pins...")
gpio = wiringpi2.GPIO(wiringpi2.GPIO.WPI_MODE_GPIO)  
gpio.pinMode(shutterpin,gpio.OUTPUT)  
gpio.pinMode(motorpinA,gpio.OUTPUT)
gpio.pinMode(motorDirection,gpio.OUTPUT)
gpio.pinMode(MS1Pin, gpio.OUTPUT)
gpio.pinMode(MS2Pin, gpio.OUTPUT)
gpio.pinMode(MS3Pin, gpio.OUTPUT)
gpio.digitalWrite(motorpinA,gpio.LOW)
gpio.digitalWrite(MS1Pin,gpio.LOW)
gpio.digitalWrite(MS2Pin,gpio.LOW)
gpio.digitalWrite(MS3Pin,gpio.LOW)

# I couldnt seem to get at pin 252 for the backlight using the usual method above, 
# but this seems to work
#os.system("echo 252 > /sys/class/gpio/export") #commented out, no HAT
#os.system("echo 'out' > /sys/class/gpio/gpio252/direction") #commented out, no HAT
#os.system("echo '1' > /sys/class/gpio/gpio252/value") #commented out, no HAT

print("Load Settings")
loadSettings() # Must come last; fiddles with Button/Icon states

print ("loading background..")
img    = pygame.image.load("icons/StackerPi.png")

if img is None or img.get_height() < 240: # Letterbox, clear background
  screen.fill(0)
if img:
  screen.blit(img,
    ((320 - img.get_width() ) / 2,
     (240 - img.get_height()) / 2))
pygame.display.update()
sleep(2)

# Main loop ----------------------------------------------------------------

signal.signal(signal.SIGTERM, signal_handler)

print ("mainloop..")
while(True):

  # Process touchscreen input
  while True:
    for event in pygame.event.get():
      if(event.type is MOUSEBUTTONDOWN):
        pos = pygame.mouse.get_pos()

        for b in buttons[screenMode]:
          if b.selected(pos):
	    break
	  else:
	    continue
#
# Added Esc key elegant exit from StackerPi.
# Added keyboard key, with repeating key, movement of the camera platform. Left arrow moves
# platform back, right arrow moves platform forwards, up arrow moves platform forward by
# 100 steps and down arrow moves the platform back 100 steps. Note that direction of the
# platform is dependent on which linear actuator drive shaft you use and which end your working from
#
      elif (event.type is KEYDOWN) and (event.key == 275): # jog platform left one step
	  motorCallback(1)
      elif (event.type is KEYDOWN) and (event.key == 276): # jog platform right one step
	  motorCallback(2)
      elif (event.type is KEYDOWN) and (event.key == 273): # jog platform left 100 steps
	    motorCallback(3)
      elif (event.type is KEYDOWN) and (event.key == 274): # jog platform right 100 steps
	    motorCallback(4)
      
      elif(((event.type is KEYDOWN) and (event.key is K_ESCAPE)) or event.type is QUIT):
	pygame.quit()
	sys.exit() # elegant exit added

    if screenMode >= 0 or screenMode != screenModePrior: break


  if img is None or img.get_height() < 240: # Letterbox, clear background
    screen.fill(0)
  if img:
    screen.blit(img,
      ((320 - img.get_width() ) / 2,
       (240 - img.get_height()) / 2))

  # Overlay buttons on display and update
    for i,b in enumerate(buttons[screenMode]):
	b.draw(screen)
	
    if screenMode == 3:
	if depressed == -1:
	    depressed = depmem
	z=1
	for x in range(6):
	    for y in range(5):
		if depressed == z:
		    screen.blit(butdown, ((x+1)*45, (y+1)*40))
		    z += 1
		else:
		    screen.blit(butup, ((x+1)*45, (y+1)*40))
		    z += 1
	
  if screenMode == 2:
    myfont = pygame.font.SysFont("Arial", 50)
    label = myfont.render(numberstring, 1, (255,255,255))
    screen.blit(label, (10, 2))
    
  if screenMode == 1:
    myfont = pygame.font.SysFont("Arial", 30)
    label = myfont.render("uStp|Mstp:1/" , 1, (255,255,255)) # Display returned microstep and macrostep
    screen.blit(label, (10, 10))
    label = myfont.render("Slice:" , 1, (255,255,255)) # Display the Dof slice in mm
    screen.blit(label, (10, 50))
    label = myfont.render("Travel:" , 1, (255,255,255)) # Display the total platform movement in mm
    screen.blit(label, (10, 90))
    label = myfont.render("Steps:" , 1, (255,255,255)) # Display the number of Steps [Frames] chosen
    screen.blit(label, (10,130))

    label = myfont.render(str(stepsize) + "|" + str(macrostep) , 1, (255,255,255)) 
    screen.blit(label, (190, 10)) 
    label = myfont.render(str(90.0/200.0/5.18/stepsize*macrostep)[:6] + " mm" , 1, (255,255,255)) #changed ms to mm
    screen.blit(label, (110, 50)) 
    label = myfont.render(str(v['Images']*90.0 / 200.0 / 5.18 / stepsize * macrostep)[:6] + " mm" , 1, (255,255,255)) #changed ms to mm
    screen.blit(label, (110, 90))
    label = myfont.render(str(v['Images']) , 1, (255,255,255))
    screen.blit(label, (140,130)) 

  if screenMode == 0:
    myfont = pygame.font.SysFont("Arial", 30)
    label = myfont.render("Slice:" , 1, (255,255,255)) # Display the Dof slice in mm
    screen.blit(label, (10, 10))
    label = myfont.render("Travel:" , 1, (255,255,255)) # Display the total platform movement in mm
    screen.blit(label, (10, 50))
    label = myfont.render("Steps:" , 1, (255,255,255)) # Display the number of Steps [Frames] chosen
    screen.blit(label, (10, 90))
    label = myfont.render("Remaining:" , 1, (255,255,255)) # Display remining time
    screen.blit(label, (10,130))

    label = myfont.render(str(90.0/200.0/5.18/stepsize*macrostep)[:6] + " mm" , 1, (255,255,255)) #changed ms to um
    screen.blit(label, (160, 10))
    label = myfont.render(str(v['Images']*90.0 / 200.0 / 5.18 / stepsize * macrostep)[:6] + " mm" , 1, (255,255,255)) #changed ms to mm
    screen.blit(label, (160, 50))
    label = myfont.render(str(currentframe) + " of " + str(v['Images']) , 1, (255,255,255))
    screen.blit(label, (160, 90))
    setStepSize(int(v['Pulse']))

    intervalLength = float(((settling_time) + (shutter_length) + pause + 0.01*macrostep))
    remaining = float((intervalLength * (v['Images'] - currentframe)))
    sec = timedelta(seconds=int(remaining))
    d = datetime(1,1,1) + sec
    remainingStr = "%dh%dm%ds" % (d.hour, d.minute, d.second)

    label = myfont.render(remainingStr , 1, (255,255,255))
    screen.blit(label, (160, 130))
	
  pygame.display.update()
  
  screenModePrior = screenMode

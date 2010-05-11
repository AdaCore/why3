from sys import stderr 

class Ansi:
    """ANSI control sequences control"""
    CSI = "\x1B["

    # colors
    Black = "0"
    Red = "1"
    Green = "2"
    Yellow = "3"
    Blue = "4"
    Magenta = "5"
    Cyan = "6"
    White = "7"
    Reset = "9"

    # effects
    bold = "1"
    reset = "0"
    underline = "4"
    blinkSlow = "5"
    blinkFast = "6"
    negative = "7"
    normal = "22"
    notUnderlined = "24"

    # fore|back ground
    foreground = "3"
    background = "4"


def colorize( s, color = "reset", pos = "foreground", *args ):
    "applies changes to the string given"
    prefix = Ansi.CSI + getattr( Ansi, pos, Ansi.foreground) + getattr( Ansi, color, Ansi.reset )
    suffix = Ansi.CSI + "m"
    for item in args:
        prefix += ";" + getattr( Ansi, item, Ansi.normal )
    prefix += "m"
    return prefix + s + suffix




def inBlue( s, bold = False, pos = "foreground" ):
    args = []
    if bold:
        args.append( "bold" )
    return colorize( s, "Blue", pos, *args )

def inGreen( s, bold = False, pos = "foreground" ):
    args = []
    if bold:
        args.append( "bold" )
    return colorize( s, "Green", pos, *args )

def inRed( s, bold = False, pos = "foreground" ):
    args = []
    if bold:
        args.append( "bold" )
    return colorize( s, "Red", pos, *args )

def inBlack( s, bold = False, pos = "foreground" ):
    args = []
    if bold:
        args.append( "bold" )
    return colorize( s, "Black", pos, *args )

def inNormal( s, bold = False, pos = "foreground" ):
    "uses normal color"
    args = []
    if bold:
        args.append( "bold" )
    return colorize( s, "Reset", pos, *args )

class Log:
    logStream = stderr

    @classmethod
    def log( self, s, bold=False ):
        """
        >>> Log.setLogStream( sys.stdout )
        >>> Log.log( 'coin' )
        coin
        >>> Log.setLogStream( file('/dev/null', 'w') )
        >>> Log.log( 'pan' )
        """
        print >> self.logStream, ansi.inNormal( s, bold= bold )

    @classmethod
    def logImportant( self, s, bold=False ):
        "prints in reversed blue"
        print >> self.logStream, ansi.inBlue( s, bold=bold, pos="background" )

    @classmethod
    def logSoft( self, s ):
        "prints in blue"
        print >> self.logStream, inBlue( s )

    @classmethod
    def logFail( self, s ):
        "for fails, print in red"
        print >> self.logStream, ansi.inRed( s, bold=True )

    @classmethod
    def logCritical( self, s ):
        "for critical warning, very visible !"
        print >> self.logStream, inRed( s, pos="background", blink=1 )

    @classmethod
    def setLogStream( self, logStream ):
        self.logStream = logStream


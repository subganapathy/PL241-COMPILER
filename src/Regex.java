import java.util.regex.*;
import java.io.*;
import parser.Parser;
public  class Regex {

	/**
	 * @param args
	 */
	//ident pattern matcher
	private static final String sWordChar = "[a-zA-Z0-9]+";
	private static final String sIdent = "[a-zA-z]" + sWordChar;
	private static Pattern sIdentPattern = Pattern.compile( sIdent );
	private static Matcher sIdentMatcher = sIdentPattern.matcher("");
	
	//number pattern matcher
	private static final String sNumChar = "[0-9]+";
	private static final String sNum = "[0-9]" + sNumChar;
	private static Pattern sNumPattern = Pattern.compile( sNumChar );
	private static Matcher sNumMatcher = sNumPattern.matcher("");
	
	//call pattern matcher
	private static final String sCallChar = "call ";
	private static Pattern sCallPattern = Pattern.compile( sCallChar );
	private static Matcher sCallMatcher = sCallPattern.matcher("");
	
	public static String sInputFile =  "./testProgs/test002.txt";
	//parameter used by the file read below
	private static String mFilename;
	private static BufferedReader mReader;
	
	
	//invariants of this parsing: every parser fun returns number of spaces in front + what its parsed length
	// running length updated after the corresponding character has been consumed
	// no longer uses substrings so a single pass across the array of chars
	public static void main  (String[] args) throws Exception {
		// TODO Auto-generated method stub
		
		Parser theParser = new Parser( sInputFile );
		theParser.parse();
	//	String str = start_reading( sInputFile );
		int start = 0;
		/*while( null != str ){
			int len = expPatternMatcher( str, start );
			if( 0 != len ){
				String subStr = str.substring(0, len );
				System.out.println( subStr );
			}

			str = next_line();
		}*/

	}
	//all the matcher functions below have the invariant that 
	//they return the match at the start of the string str if one exists
	private static int identPatternMatcher( String str, int start ) {
		sIdentMatcher.reset( str );
		int runningLength = 0;
		int numSpaces = stripSpaces( str, start );
		runningLength += numSpaces;
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return 0;
		if( Character.isLetter( str.charAt( nonSpace ) ) && sIdentMatcher.find( nonSpace ) == true ){
			String currentGrp = sIdentMatcher.group();
			runningLength += currentGrp.length();
			nonSpace += currentGrp.length();
			numSpaces = stripSpaces( str, nonSpace );
			if( str.length() <= nonSpace || str.charAt( nonSpace ) != '[' )
				return runningLength;
			
			while(   str.length() > nonSpace && str.charAt( nonSpace ) == '[' ){
				runningLength += numSpaces;
				int expPos = expressionCharMatcher( str, nonSpace, '[', ']' );
				nonSpace += expPos;
				runningLength += expPos;
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace += numSpaces;
			}
			return runningLength;
		}
		return runningLength;
	}
	
	private static int numPatternMatcher( String str, int start ) {
		sNumMatcher.reset( str );
		int runningLength = 0;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		runningLength += numSpaces;
		if( nonSpace == str.length() ) return 0;
		if( str.charAt( nonSpace ) == '-' ){
			++runningLength;
			++nonSpace;
		}
		if( sNumMatcher.find( nonSpace ) == true ) {
			String currentGrp = sNumMatcher.group();
			runningLength += currentGrp.length();
			return runningLength;
		}
		return runningLength;
	}
	
	private static int stripSpaces( String str, int start ) {
		int i = start;
		int len = str.length();
		while( i < len && str.charAt( i ) == ' ')
			i++;
		return i - start;
	}
	
	private static Boolean isDigit( String str, int charIndex ) {
		return '0' <= str.charAt( charIndex ) && str.charAt( charIndex ) <= '9';
	}
	
	private static int expressionCharMatcher( String str, int start, char begin, char end ){
		int runningLength = 0;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		runningLength += numSpaces;
		if( begin == str.charAt( nonSpace ) ){
			++nonSpace;++runningLength;
			int expPos = expPatternMatcher( str, nonSpace );
			if( expPos == 0 ) {
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace +=  numSpaces;
				runningLength += numSpaces;
				if( str.charAt( nonSpace ) == end ){
					++runningLength;
					return runningLength;
				}
				return runningLength; //compile error;			
			}
			nonSpace += expPos;
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += ( expPos + numSpaces );
			while( str.charAt( nonSpace ) == ',' ){
				++nonSpace;
				++runningLength;
				expPos = expPatternMatcher( str, nonSpace );
				if( 0 == expPos ) return 0; //this is compile error
				nonSpace += expPos;
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace += numSpaces;
				runningLength += ( expPos + numSpaces );
				
			}
			if( end == str.charAt( nonSpace ) ){
				nonSpace++; runningLength++;
				return runningLength;
			}
		}
		return runningLength;
	}
	
	private static int functionCallPatternMatcher( String str, int start ) {
		int runningLength = 0;
		int idenPos = identPatternMatcher( str, start );
		runningLength += idenPos;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces + idenPos;
		runningLength += numSpaces;
		if( str.charAt( nonSpace ) == '(' ){
			int argPos = expressionCharMatcher( str, nonSpace, '(', ')' );
			runningLength +=  argPos;
		}
		
		return runningLength;
	}
	private static int factorPatternMatcher( String str, int start ) {
		int runningLength = 0;
		//int 
		int numSpaces = stripSpaces( str, start );
		int nonSpace = numSpaces + start;
		runningLength += numSpaces;
		//sCallMatcher.reset( str );
		if( true == str.startsWith( sCallChar, nonSpace ) ){
			nonSpace += sCallChar.length();
			runningLength += sCallChar.length();
			int funcPatternMatcher = functionCallPatternMatcher( str, nonSpace );
			runningLength += funcPatternMatcher;
			return runningLength;
			
		}
		else if( '(' == str.charAt( nonSpace ) ){
			int expPos = expressionCharMatcher( str, nonSpace, '(', ')' );
			nonSpace += expPos;
			runningLength += expPos;
			return runningLength;
				
		}
		else if( isDigit( str, nonSpace) || str.charAt( nonSpace ) == '-' ){
			int numPos = numPatternMatcher( str, nonSpace );
			runningLength += numPos;
			return runningLength;
		}
		else{
			//good old designator or identmatcher
			int desigPos = identPatternMatcher( str, nonSpace );
			if( 0 == desigPos ) return runningLength;
			runningLength += desigPos;
			return runningLength;
		}
		
	}
	private static int termPatternMatcher( String str, int start ){
		int runningLength = 0;
		int termPos = factorPatternMatcher( str, start );
		if( 0 == termPos ) return runningLength;
		start += termPos;
		//String termStripped = str.substring( termPos );
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return termPos;
		runningLength = (termPos + numSpaces);
		while( str.charAt( nonSpace ) == '*' || str.charAt( nonSpace ) == '/' ){
			++runningLength;++nonSpace;
			termPos = factorPatternMatcher( str, nonSpace );
			if( 0 == termPos ) return 0; //this is a syntax error??
			nonSpace += termPos;
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += (numSpaces + termPos);
			if( nonSpace == str.length() ) return runningLength;
			
		}
		
		return runningLength;
	}
	private static int expPatternMatcher( String str, int start ) {
		int runningLength = 0;
		int termPos = termPatternMatcher( str, start );
		if( 0 == termPos ) return 0;
		start += termPos;
		//String termStripped = str.substring( termPos );
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return termPos;
		runningLength = (numSpaces + termPos);
		while( str.charAt( nonSpace ) == '+' || str.charAt( nonSpace ) == '-' ){
			++runningLength;
			termPos = termPatternMatcher( str, ++nonSpace );
			if( 0 == termPos ) return 0; //this is a syntax error??
			nonSpace += termPos;
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += (numSpaces + termPos);
			if( nonSpace == str.length() ) return runningLength;
			
		}
		
		return runningLength;		
	}
	private static String start_reading( String filename ){
		try {
		    if( mReader != null && mReader.ready() )
		    	mReader.close();
		    mReader = new BufferedReader( new FileReader( filename ) );
		    mFilename = filename;
		    String str;
		    str = mReader.readLine();
		    if( null == str ){
		    	mReader.close();
		    	return null;
		    }
		    return str;
		} catch (IOException e) {
			return null;
		}
	}
	
	private static String next_line( ){
		try {
		    
		    if( !mReader.ready() )
		    	return null;
		    String str;
		    str = mReader.readLine();
		    if( null == str ){
		    	mReader.close();
		    	return null;
		    }
		    return str;
		} catch (IOException e) {
			return null;
		}
	}

}

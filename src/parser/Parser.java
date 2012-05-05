package parser;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.regex.*; 
import intermediateObjects.InterRep;
import intermediateObjects.InterRep.CodeBlock;
public class Parser {

	public static class NamedObject {
		public int mRemaining;
		public Object mObject;
		public Boolean mObjectValid;
		
		public NamedObject( int remaining, Object object) {
		this.mRemaining = remaining;
		this.mObject = object;
		mObjectValid = true;
		}
		public NamedObject(){
			mObjectValid = false;
		}
		public static NamedObject makeDefaultObject( int remaining ){
			NamedObject ret = new NamedObject();
			ret.mObject = new Object();
			ret.mRemaining = remaining;
			return ret;
		}
	}
	public static class ContextBlock{
		private String myContext;
		public ContextBlock(){
			super();
			myContext = new String();
		}
		
		public String getContext() {
			return myContext;
		}
		public String getContextFull(){
			return myContext + "LINE: " + FileUtils.lastReadLine + ": LINENUM: " + Integer.toString( FileUtils.lastReadLineNum );
		}
		
		public void setContext( String curContext ){
			myContext = curContext;
		}
	}
	
	public static class ContextSetter{
		String savedContext = new String();
		public ContextSetter( String context ){
			savedContext = globalContext.getContext();
			globalContext.setContext( context );
		}
		public void resetContext() {
			globalContext.setContext( savedContext );
		}
	}
	public static ContextBlock globalContext = new ContextBlock();
	public static final String[ ] sErrors = { "SYNTAX ERROR: Expected '%0', but found '%1'", "VARIABLE REDEFINITION: '%0'" };
	public static final int sVarDeclSyntax = 0;
	public static final int sVarRedefn = 1;
	public static String mStr;
	public static int mStart;
	
	public static HashMap< String, stmParser > mParseTable;
	public static Set< String > mKeywordTable;
	private void initializeMap(){
		mParseTable = new HashMap< String, stmParser > ();
		//mParseTable.put( "main", new MainStmParser() );
		mParseTable.put("let", new AssignmentStmParser() );
		mParseTable.put("call", new FnCallStmParser() );
		mParseTable.put( "if", new IfElseStmParser() );
		mParseTable.put("while", new WhileStmParser() );
		mParseTable.put("return", new ReturnStmParser() );
		mParseTable.put("//", new CommentStmParser() );
		mParseTable.put("#", new CommentStmParser() );
		mKeywordTable = mParseTable.keySet();
	}

	public Parser( String filename ){
		super();
		initializeMap();
		FileUtils.startReading( filename );
	}

	public void parse( ) throws Exception {
		InterRep.globalSymTab.Init();
		MainStmParser mainParser = new MainStmParser();
		EnsureStringPresent( 0 );
		NamedObject retval = mainParser.parse();
		if( retval.mObjectValid ){
			InterRep.Computation compObj = ( InterRep.Computation ) retval.mObject;
			ArrayList< CodeBlock > lr = compObj.returnIR();
			/*for( int i = 0; i < lr.size(); ++i ){
				String sr = InterRep.CodeBlock.serializeMe( lr.get( i ) );
				System.out.print(sr);
			}*/
		}
	}
public static abstract class stmParser{
	abstract NamedObject parse() throws Exception;
}

public static class CommentStmParser extends stmParser{
	public NamedObject parse() throws Exception{
		int nonSpace = SkipThisLine( mStart );
		nonSpace = EnsureStringPresent( nonSpace );
		return NamedObject.makeDefaultObject( 0 );
	}
}
public static class ExpressionStmParser extends stmParser{
	public NamedObject parse() throws Exception{
		int nonSpace = EnsureStringPresent( mStart );
		NamedObject obj = ParseUtils.expPatternMatcher( mStr, nonSpace );
		nonSpace += obj.mRemaining;
		nonSpace = EnsureStringPresent( nonSpace );
		if( obj.mObjectValid )
			return new NamedObject( 0, new InterRep.ExpressionStm( ( InterRep.Expression ) obj.mObject ) );
		return NamedObject.makeDefaultObject( 0 );
	}
}
public static class AssignmentStmParser extends stmParser{
	public NamedObject parse() throws Exception{
		InterRep.Designator theDesig;
		InterRep.Expression theExp;
		int nonSpace = EnsureStringPresent( mStart );
		NamedObject desigObj = ParseUtils.identPatternMatcher( mStr, nonSpace );
		nonSpace += desigObj.mRemaining;
		if( !desigObj.mObjectValid ) throw new Exception("Ill-formed Designator @: " + globalContext.getContextFull() );
		theDesig = ( InterRep.Designator ) desigObj.mObject;
		final String kLetPattern = "<-";
		nonSpace = EnsureStringPresent( nonSpace );
		if( mStr.startsWith( kLetPattern, nonSpace ) ){
			nonSpace += kLetPattern.length();
		}
		NamedObject expObj = ParseUtils.expPatternMatcher( mStr,  nonSpace );
		nonSpace += expObj.mRemaining;
		nonSpace = EnsureStringPresent( nonSpace );
		if( !expObj.mObjectValid ) throw new Exception("Ill-formed Expression: " + globalContext.getContextFull() );
		theExp = ( InterRep.Expression ) expObj.mObject;
		
		return new NamedObject( 0, new InterRep.AssignmentStm( theDesig, theExp ) );
	}
}

public static class FnCallStmParser extends stmParser{
	public NamedObject parse() throws Exception {
		int nonSpace = EnsureStringPresent( mStart );
		NamedObject fnCallObj = ParseUtils.functionCallPatternMatcher( mStr, nonSpace );
		nonSpace += fnCallObj.mRemaining;
		nonSpace = EnsureStringPresent( nonSpace );
		return new NamedObject( 0, fnCallObj.mObject );
	}
}

public static class IfElseStmParser extends stmParser{
	public NamedObject parse() throws Exception {
		ContextSetter setcont = new ContextSetter( "Parsing If-Else statements at : " + globalContext.getContext() );
		NamedObject theRel = ParseUtils.relPatternMatcher( mStr,  mStart );
		InterRep.RelationOperation theRelExp;
		ArrayList< InterRep.stm > theStmList = new ArrayList< InterRep.stm >();
		ArrayList< InterRep.stm > theElseList = new ArrayList< InterRep.stm >();
		int nonSpace = EnsureStringPresent( mStart + theRel.mRemaining );
		if( !theRel.mObjectValid )throw new Exception("Ill-formed condition @: " + globalContext.getContextFull() );
		
		theRelExp = ( InterRep.RelationOperation ) theRel.mObject;
		final String kThen = "then";
		final String kElse = "else";
		final String kFi = "fi";
		if( mStr.startsWith( kThen, nonSpace ) )
			nonSpace += kThen.length();
		else
			throw new Exception("Then statement missing @: " + globalContext.getContextFull() );
		nonSpace = EnsureStringPresent( nonSpace );
		
		StmSeqParser theParser = new StmSeqParser();
		NamedObject theParseObject = theParser.parse();
		nonSpace = EnsureStringPresent(mStart);
		if( theParseObject.mObjectValid ){
			theStmList = ( ArrayList< InterRep.stm > )theParseObject.mObject;
		}
		if( mStr.startsWith( kElse, nonSpace ) ){
			nonSpace += kElse.length();
			nonSpace = EnsureStringPresent( nonSpace );
			theParseObject = theParser.parse();
			nonSpace = EnsureStringPresent(mStart);
			if( theParseObject.mObjectValid ){
				theElseList = ( ArrayList< InterRep.stm > )theParseObject.mObject;
			}
		}
		if( mStr.startsWith( kFi, nonSpace ) ){
			nonSpace += kFi.length();
			nonSpace = EnsureStringPresent( nonSpace );
			if( mStr.charAt( nonSpace ) == ';' ){
				++nonSpace;
				nonSpace = EnsureStringPresent( nonSpace );
			}
			
		}
		else
			throw new Exception("fi statement missing @: " + globalContext.getContextFull() );
		setcont.resetContext();
		return new NamedObject( 0, new InterRep.IfStm( theRelExp, theStmList, theElseList  ) );
	}
}

public static class WhileStmParser extends stmParser{
	public NamedObject parse() throws Exception {
		ContextSetter setcont = new ContextSetter( "parsing While block in " + globalContext.getContext() );
		NamedObject theRel = ParseUtils.relPatternMatcher( mStr,  mStart );
		InterRep.RelationOperation theRelExp;
		ArrayList< InterRep.stm > theStmList = new ArrayList< InterRep.stm >();
		int nonSpace = EnsureStringPresent( mStart + theRel.mRemaining );
		theRelExp = ( InterRep.RelationOperation ) theRel.mObject;
		
		final String kDo = "do";
		final String kOd = "od";
		if( mStr.startsWith( kDo, nonSpace ) ){
			nonSpace += kDo.length();
			nonSpace = EnsureStringPresent( nonSpace );
			StmSeqParser theParser = new StmSeqParser();
			NamedObject theObj = theParser.parse();
			nonSpace = EnsureStringPresent( mStart );
			if( theObj.mObjectValid )
				theStmList = ( ArrayList< InterRep.stm > )theObj.mObject;
			
			if( mStr.startsWith( kOd, nonSpace ) ){
				nonSpace += kOd.length();
				nonSpace = EnsureStringPresent( nonSpace );
				if( mStr.charAt( nonSpace ) == ';' ){
					++nonSpace;
					nonSpace = EnsureStringPresent( nonSpace );
				}
			}
			else
				throw new Exception("No matching Od statement found @: " + globalContext.getContextFull() );
		}
		setcont.resetContext();
		return new NamedObject( 0, new InterRep.WhileStm( theRelExp, theStmList ) );
	}
}

public static class ReturnStmParser extends stmParser{
	public NamedObject parse()throws Exception {
		int nonSpace = EnsureStringPresent( mStart );

		InterRep.Expression theExp;
		
		NamedObject expObj = ParseUtils.expPatternMatcher( mStr, nonSpace );
		nonSpace += expObj.mRemaining;
		nonSpace = EnsureStringPresent( nonSpace );
		if( expObj.mObjectValid == false )throw new Exception("Ill formed return expression @ " + globalContext.getContextFull() );
		theExp = ( InterRep.Expression )expObj.mObject;
		
		return new NamedObject( 0, new InterRep.ReturnStm( theExp ) );
		
	}
}

public static class DeclStmParser extends stmParser{
	private Boolean mArray;
	ArrayList< String > identList = new ArrayList< String >();
	Hashtable< String, ArrayList< Integer > > arrayList = new Hashtable< String, ArrayList< Integer > >();
	public DeclStmParser( Boolean array ){
		mArray = array;
	}
	
	
	private Boolean checkDuplicate( String variable ) throws Exception{
		Boolean dup = false;
		if( identList.contains( variable ) )
			dup = true;
		else if( arrayList.containsKey( variable ) )
			dup = true;
		if( dup ){
			String error = sErrors[ sVarRedefn ];
			error = error.replaceFirst("%0", variable );
			throw new Exception( error );
		}
		return false;
	}
	
	public NamedObject parse() throws Exception{
		int nonSpace = EnsureStringPresent( mStart );
		
		final String kArray = "array";
		final String kVar = "var";
		Boolean isArray = mStr.startsWith( kArray, nonSpace );
		if( isArray )
			nonSpace += kArray.length();
		Boolean isVar = mStr.startsWith( kVar, nonSpace );
		if( isVar )
			nonSpace += kVar.length();
		nonSpace = EnsureStringPresent( nonSpace );
		while( isArray || isVar ){
			if( isArray ){
				ArrayList< Integer > dim = new ArrayList< Integer >();
				while( '[' == mStr.charAt( nonSpace ) ){
					++nonSpace;
					NamedObject numVal = ParseUtils.numPatternMatcher( mStr, nonSpace );
					if( numVal.mObjectValid == false ) return NamedObject.makeDefaultObject( -1 );
					nonSpace += numVal.mRemaining;
					dim.add( ( Integer ) numVal.mObject );
					nonSpace = EnsureStringPresent( nonSpace );
					if( ']' == mStr.charAt( nonSpace ) ){
						++nonSpace;	
					}
					else{	
						throw new Exception( "Invalid identifiers specified for var declaration @: " + globalContext.getContextFull() );
					}
				}
					NamedObject identListObject = ParseUtils.IdentCharMatcher( mStr, nonSpace, (char)0, ';');
					nonSpace += identListObject.mRemaining;
					ArrayList< InterRep.Designator > idents = ( ArrayList< InterRep.Designator > )identListObject.mObject;
					for( int i = 0; i < idents.size(); ++i ){
						if( idents.get( i ).getMIdentifier() != null && !checkDuplicate( idents.get( i).getMIdentifier() ) )
							arrayList.put( idents.get( i ).getMIdentifier(), dim );
					}
				}
			else if ( isVar ){
				NamedObject identListObject = ParseUtils.IdentCharMatcher( mStr, nonSpace, (char)0, ';');
				nonSpace += identListObject.mRemaining;
				if( identListObject.mObjectValid == false ){
					throw new Exception( "Invalid identifiers specified for var declaration @: " + globalContext.getContextFull() );
				}
				ArrayList< InterRep.Designator > idents = ( ArrayList< InterRep.Designator > )identListObject.mObject;
				for( int i = 0; i < idents.size(); ++i ){
					if( idents.get( i ).getMIdentifier() != null&& !checkDuplicate( idents.get( i).getMIdentifier() ) )
						identList.add( idents.get( i ).getMIdentifier() );
				}
			}
			nonSpace = EnsureStringPresent( nonSpace );
			isArray = mStr.startsWith( kArray,  nonSpace );
			if( isArray )
				nonSpace += kArray.length();
			isVar = mStr.startsWith( kVar, nonSpace );
			if( isVar )
				nonSpace += kVar.length();
			nonSpace = EnsureStringPresent(nonSpace);
		}
		
		
		return new NamedObject( 0, new InterRep.VarDecl( identList, arrayList ) );
	}
}

public static int EnsureStringPresent( int start ) throws Exception {
	if( mStr == null || mStr.length() <= mStart || mStr.length() <= start ){
		mStr = FileUtils.nextLine();
		mStart = 0;
		start = 0;
		if( null == mStr ) throw new Exception("error at : " + globalContext.getContext() );
	}
	int numSpaces = ParseUtils.stripSpaces( mStr, start );
	start += numSpaces;
	while( start >= mStr.length() ){
		mStr = FileUtils.nextLine();
		if( null == mStr ) return -1;
		mStart = 0;
		start = ParseUtils.stripSpaces( mStr,  0 );
	}
	if( mStart != start ) mStart = start; //this will catch a bunch of bugs due to index not being set properly.
	return start;
}

public static int SkipThisLine( int start ) throws Exception{
	mStr = FileUtils.nextLine();
	mStart = 0;
	if( null == mStr ) throw new Exception("error at : " + globalContext.getContext() );
	return 0;
}

public static void SetStartIndex( int nonSpace ){
	mStart = nonSpace;
}

public static class FunStmParser extends stmParser{
	private Boolean mFunction;
	public FunStmParser( Boolean function ){
		mFunction = function;
	}
	public NamedObject parse() throws Exception {
		ContextSetter setcont = new ContextSetter( "Parsing function declaration: " );
		final String kFn = "function";
		final String kProc = "procedure";
		Hashtable< String, InterRep.FunDecl > fnDeclList = new Hashtable< String, InterRep.FunDecl >();
		int nonSpace = EnsureStringPresent( mStart );
		Boolean isFn =   mStr.startsWith( kFn, nonSpace ) ;
		Boolean isProc = mStr.startsWith( kProc, nonSpace );
		if( !isFn && !isProc )
			return NamedObject.makeDefaultObject( 0 );
		if( isFn )
			nonSpace += kFn.length();
		else if( isProc )
			nonSpace += kProc.length();
		nonSpace = EnsureStringPresent( nonSpace );
		//ContextSetter setcont = new ContextSetter( "Parsing function declaration: " );
		while( isFn  || isProc ){
			String funcName = new String();
			ArrayList< String > formalParams = new ArrayList< String >();
			ArrayList< InterRep.stm > stmList = new ArrayList< InterRep.stm >();
			InterRep.VarDecl varDecls = new InterRep.VarDecl( new ArrayList< String >(), new Hashtable< String, ArrayList< Integer > >() );
			
			//get the function name.
			NamedObject fnNameObj = ParseUtils.identPatternMatcher( mStr,  nonSpace );
			if( fnNameObj.mObjectValid == false ){
				throw new Exception( "Invalid Function name token found: " + globalContext.getContextFull() );
			}
			funcName = (( InterRep.Designator ) fnNameObj.mObject).getMIdentifier();
			setcont.resetContext();
			setcont = new ContextSetter( "Parsing function: " + funcName );
			String savedContext = InterRep.globalSymTab.getCurrentContext();
			InterRep.globalSymTab.SetCurrentContext( funcName );
			nonSpace += fnNameObj.mRemaining;
			
			//get the formal Params
			nonSpace = EnsureStringPresent( nonSpace );
			NamedObject formalParamsObj = ParseUtils.IdentCharMatcher( mStr, nonSpace, '(', ')' );
			if( formalParamsObj.mObjectValid ){
				ArrayList< InterRep.Designator > desig = ( ArrayList< InterRep.Designator > )( formalParamsObj.mObject );
				formalParams = InterRep.globalSymTab.identList( desig );
			}
			nonSpace += formalParamsObj.mRemaining;
			nonSpace = EnsureStringPresent( nonSpace );
			if( mStr.charAt( nonSpace ) == ';' )
				++nonSpace;
			nonSpace = EnsureStringPresent( nonSpace );
			
			DeclStmParser theVarParser = new DeclStmParser( true );
			NamedObject varDeclObj = theVarParser.parse();
			if( varDeclObj.mObjectValid ){
				varDecls = ( InterRep.VarDecl ) varDeclObj.mObject;
				if( formalParams.size() > 0 )
					varDecls.AddFormals( formalParams );
			}
			nonSpace = mStart;
			nonSpace = EnsureStringPresent( nonSpace );
			
			StmSeqParser stmSeqParser = new StmSeqParser();
			NamedObject stmSeqObj = stmSeqParser.parse();
			if( stmSeqObj.mObjectValid ){
				stmList = ( ArrayList< InterRep.stm > )stmSeqObj.mObject;
			}
			nonSpace = mStart;
			//nonSpace = EnsureStringPresent( nonSpace );
			
			InterRep.FormalParam formParam = new InterRep.FormalParam( formalParams );
			InterRep.FunBody funBody = new InterRep.FunBody( varDecls, stmList );
			InterRep.FunDecl funDecl = new InterRep.FunDecl( isFn, funcName, formParam, funBody );
			fnDeclList.put( funcName, funDecl );
			nonSpace = EnsureStringPresent( nonSpace );
			isFn =   mStr.startsWith( kFn, nonSpace ) ;
			isProc = mStr.startsWith( kProc, nonSpace );
			InterRep.globalSymTab.SetCurrentContext( savedContext );
			if( !isFn && !isProc )
				break;
			if( isFn )
				nonSpace += kFn.length();
			else if( isProc )
				nonSpace += kProc.length();
			nonSpace = EnsureStringPresent( nonSpace );
			setcont.resetContext();
		}
		setcont.resetContext();
		return  new NamedObject( 0, fnDeclList );
		
	}
}

public static class StmSeqParser extends stmParser{
	private String startsWith( int offset){
		String start = new String();
		Iterator< String > theIter = Parser.mKeywordTable.iterator();
		while( theIter.hasNext() ){
			String current = theIter.next();
			if( mStr.startsWith( current,  offset  ) ){
				return current;
			}
		}
		return start;
	}
	private stmParser getParser( String key ){
		stmParser theParser = mParseTable.get( key );
		return theParser;
	}
	public NamedObject parse() throws Exception {
		ContextSetter setcont = new ContextSetter( "parsing statement sequence ");
		int nonSpace = EnsureStringPresent( mStart );
		//remove open bracket if any
		boolean onlyOnce = false;
		if( mStr.charAt( nonSpace ) == '{' )
			++nonSpace;
		else 
			onlyOnce = true;
		nonSpace = EnsureStringPresent( nonSpace );
		String current = startsWith( nonSpace );
		ArrayList< InterRep.stm > stmList = new ArrayList< InterRep.stm >();
		
		while( !current.isEmpty() ){
			stmParser curParser;
			if( null == ( curParser = getParser( current )) ){
				ExpressionStmParser expParser = new ExpressionStmParser();
				curParser = expParser;
				//throw new Exception( "Unidentified token:" + globalContext.getContextFull() );
			}
			nonSpace += current.length();
			nonSpace = EnsureStringPresent( nonSpace );
			NamedObject parseObj = curParser.parse();
			if( parseObj.mObjectValid ){
				stmList.add( ( InterRep.stm ) parseObj.mObject );
			}
			nonSpace = EnsureStringPresent( mStart );
			if( mStr.charAt( nonSpace ) == ';' ){
				++nonSpace;
				nonSpace = EnsureStringPresent( nonSpace );
			}
			
			if( !onlyOnce && mStr.charAt(nonSpace) == '}'){
				++nonSpace;
				nonSpace = EnsureStringPresent( nonSpace );
				if( mStr.charAt( nonSpace ) == ';' ){
					++nonSpace;
					nonSpace = EnsureStringPresent( nonSpace );
				}
				break;
			}
			current = startsWith( nonSpace );
		}
		setcont.resetContext();
		return new NamedObject( 0, stmList);
		
	}
}

public static class MainStmParser extends stmParser{
	public NamedObject parse(  ) throws Exception {
		
			ContextSetter setcont = new ContextSetter("Begin Parsing");
			InterRep.globalSymTab.SetCurrentContext( "main" );
			final String kMain = "main";
			int nonSpace = EnsureStringPresent( mStart );
			if( !mStr.startsWith( kMain, nonSpace ) ){
				while( mStr.startsWith("//", nonSpace ) || mStr.startsWith("#", nonSpace ) ){
					stmParser commentParser = new CommentStmParser();
					commentParser.parse();
					nonSpace = EnsureStringPresent( mStart );
				}
				if( !mStr.startsWith( kMain, nonSpace ) )
					return NamedObject.makeDefaultObject( -1 ); //this is a compile error. TODO come up with an exception based architecture to handle compile error.
			}
				
			nonSpace += kMain.length();
			
			//now handle the typedecl stuff.
			nonSpace = EnsureStringPresent( nonSpace );
			
			DeclStmParser declParser = new DeclStmParser( true );
			NamedObject retVal =  declParser.parse(  );
			InterRep.VarDecl theDecl = new InterRep.VarDecl( new ArrayList< String >(), new Hashtable< String, ArrayList< Integer > >() );
			if( retVal.mObjectValid )
				theDecl = ( InterRep.VarDecl )retVal.mObject;
			InterRep.globalSymTab.AddContextVars( "main", theDecl );
			nonSpace = EnsureStringPresent( mStart );
			FunStmParser fnParser = new FunStmParser( true );
			Hashtable< String, InterRep.FunDecl > declList = new Hashtable< String, InterRep.FunDecl > ();
			retVal = fnParser.parse();
			if( retVal.mObjectValid )
				declList = ( Hashtable< String, InterRep.FunDecl > )retVal.mObject;
			
			nonSpace = EnsureStringPresent( mStart );
			ArrayList< InterRep.stm > stmList = new ArrayList< InterRep.stm > ();
			StmSeqParser theStmParser = new StmSeqParser();
			retVal = theStmParser.parse();
			if( retVal.mObjectValid )
				stmList = ( ArrayList< InterRep.stm > )retVal.mObject;
			InterRep.Computation compObj = new InterRep.Computation( theDecl, declList, stmList );
			return new NamedObject( 0, compObj );
			
	}
}
public static class FileUtils{
	//parameter used by the file read below
	private static String mFilename;
	private static BufferedReader mReader;
	public static String lastReadLine = new String();
	public static Integer lastReadLineNum = 0;
	public static void startReading( String filename ){
		try {
		    if( mReader != null && mReader.ready() )
		    	mReader.close();
		    mReader = new BufferedReader( new FileReader( filename ) );
		    mFilename = filename;
		} catch (IOException e) {
		}
	}
	
	private static String nextLine( ){
		try {
		    
		    if( !mReader.ready() )
		    	return null;
		    String str;
		    str = mReader.readLine();
		    if( null != str ){
		    	lastReadLine = str;
			    ++lastReadLineNum;
		    }
		    	
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
//Parser routines: these are helper routines for parsing the various  pieces of a pl241 program:
//All routines are implemented such that, they:
//1) Traverse each character only once
//2) Return a std::pair of how many characters they consumed and an Object representation of the consumed characters i.e. either an expression or call statement or array operation.
//3) Each routine consumes the space in front of the characters it is supposed to consume.
public static class ParseUtils{
	//ident pattern matcher
	private static final String sWordChar = "[a-zA-Z0-9]+";
	private static final String sIdent = "^[a-zA-Z0-9_]*$";
	private static Pattern sIdentPattern = Pattern.compile( sIdent );
	private static Matcher sIdentMatcher = sIdentPattern.matcher("");
	
	//number pattern matcher
	private static final String sNumChar = "[0-9]+";
	private static final String sNum = "[0-9]" + sNumChar;
	private static Pattern sNumPattern = Pattern.compile( sNumChar );
	private static Matcher sNumMatcher = sNumPattern.matcher("");
	
	//call pattern matcher
	private static final String sCallChar = "call ";
	
	//all the matcher functions below have the invariant that 
	//they return the match at the start of the string str if one exists
	//a failsafe so to speak.
	private static String buildIdent( String str, int start ){
		String retVal = new String();
		while( str.length() > start && Character.isLetterOrDigit( str.charAt( start ) ) ){
			retVal += str.charAt( start );
			++start;
		}
		return retVal;
	}
	private static Parser.NamedObject identPatternMatcher( String str, int start ) {
		sIdentMatcher.reset( str );
		int runningLength = 0;
		String currentGrp = new String();
		int numSpaces = stripSpaces( str, start );
		runningLength += numSpaces;
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return Parser.NamedObject.makeDefaultObject( 0 );
		if( Character.isLetter( str.charAt( nonSpace ) ) && ( currentGrp = buildIdent( str, nonSpace) ).isEmpty() == false  ){
			//currentGrp = sIdentMatcher.group();
			runningLength += currentGrp.length();
			nonSpace += currentGrp.length();
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			if( str.length() <= nonSpace || str.charAt( nonSpace ) != '[' ) {
				ArrayList< InterRep.Expression > theSkankyExpList = new ArrayList< InterRep.Expression >();
				return new Parser.NamedObject( runningLength, new InterRep.Designator( new String( currentGrp ), theSkankyExpList  ) );
			}
				
			
			else if(   str.length() > nonSpace && str.charAt( nonSpace ) == '[' ){
				runningLength += numSpaces;
				ArrayList< InterRep.Expression > theExpList = new ArrayList< InterRep.Expression >();
				while( str.length() > nonSpace && str.charAt( nonSpace ) == '[' ){
					Parser.NamedObject retVal = expressionCharMatcher( str, nonSpace, '[', ']' );
					if( !retVal.mObjectValid ){
						retVal.mRemaining += runningLength;
						return retVal;
					}
					nonSpace += retVal.mRemaining;
					runningLength += retVal.mRemaining;
					numSpaces = stripSpaces( str, nonSpace );
					nonSpace += numSpaces;
					
					ArrayList< InterRep.Expression > tempList = ( ArrayList< InterRep.Expression > )( retVal.mObject );
					if( tempList == null ) continue;
					InterRep.Expression theExp = tempList.get( 0 );
					theExpList.add( theExp );
				}
				if( null == theExpList ) theExpList = new ArrayList< InterRep.Expression >();
				return new Parser.NamedObject( runningLength, new InterRep.Designator( currentGrp, theExpList ) );
					
			}
			
		}
		return Parser.NamedObject.makeDefaultObject( runningLength );
	}
	
	private static Parser.NamedObject numPatternMatcher( String str, int start ) {
		sNumMatcher.reset( str );
		int runningLength = 0;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		runningLength += numSpaces;
		if( nonSpace == str.length() ) return  Parser.NamedObject.makeDefaultObject( 0 );
		Boolean negative = false;
		if( str.charAt( nonSpace ) == '-' ){
			++runningLength;
			++nonSpace;
			negative = true;
		}
		if( sNumMatcher.find( nonSpace ) == true ) {
			String currentGrp = sNumMatcher.group();
			runningLength += currentGrp.length();
			Integer theVal = Integer.valueOf( currentGrp );
			if( negative )
				theVal = -theVal;
			return new Parser.NamedObject( runningLength, theVal );
		}
		return Parser.NamedObject.makeDefaultObject( runningLength );
	}
	
	private static int stripSpaces( String str, int start ) {
		int i = start;
		int len = str.length();
		while( i < len && ( Character.isSpaceChar(str.charAt( i ) ) || str.charAt( i ) == '\t' ) ) //FIXME java does not recognize \t wtf
			i++;
		return i - start;
	}
	
	private static Boolean isDigit( String str, int charIndex ) {
		return '0' <= str.charAt( charIndex ) && str.charAt( charIndex ) <= '9';
	}
	
	private static Parser.NamedObject expressionCharMatcher( String str, int start, char begin, char end ){
		int runningLength = 0;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		InterRep.Expression returnedExp;
		ArrayList< InterRep.Expression  > theExpList = new ArrayList< InterRep.Expression  >();
		Parser.NamedObject theRetVal;
		runningLength += numSpaces;
		if( begin == str.charAt( nonSpace ) || begin == 0 ){
			if( 0 != begin ){
				++nonSpace;++runningLength;
			}
			theRetVal = expPatternMatcher( str, nonSpace );
			if( !theRetVal.mObjectValid ) {
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace +=  numSpaces;
				runningLength += numSpaces;
				runningLength += theRetVal.mRemaining;
				if( str.charAt( nonSpace ) == end ){
					++runningLength;
					theRetVal.mObject = theExpList;
					theRetVal.mRemaining = runningLength;
					theRetVal.mObjectValid = true;
					return theRetVal;
				}
				return Parser.NamedObject.makeDefaultObject( runningLength ); //compile error;			
			}
			nonSpace += theRetVal.mRemaining;
			theExpList.add(  ( InterRep.Expression ) theRetVal.mObject );
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += ( theRetVal.mRemaining + numSpaces );
			while( str.charAt( nonSpace ) == ',' ){
				++nonSpace;
				++runningLength;
				theRetVal = expPatternMatcher( str, nonSpace );
				if( !theRetVal.mObjectValid ) {
					theRetVal.mRemaining = runningLength;
					theRetVal.mObject = theExpList;
					return theRetVal; //this is compile error
				}
				nonSpace += theRetVal.mRemaining;
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace += numSpaces;
				runningLength += ( theRetVal.mRemaining + numSpaces );
				theExpList.add( ( InterRep.Expression  )theRetVal.mObject );
			}
			if( end == str.charAt( nonSpace ) ){
				nonSpace++; runningLength++;
				return new Parser.NamedObject( runningLength, theExpList );
			}
		}
		return Parser.NamedObject.makeDefaultObject( runningLength );
	}
	
	private static Parser.NamedObject IdentCharMatcher( String str, int start, char begin, char end ){
		int runningLength = 0;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		InterRep.Designator returnedExp;
		ArrayList< InterRep.Designator  > theExpList = new ArrayList< InterRep.Designator  >();
		Parser.NamedObject theRetVal;
		runningLength += numSpaces;
		if( begin == str.charAt( nonSpace ) || begin == 0 ){
			if( begin != 0){
				++nonSpace;++runningLength;
			}
			theRetVal = identPatternMatcher( str, nonSpace );
			if( !theRetVal.mObjectValid ) {
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace +=  numSpaces;
				runningLength += numSpaces;
				runningLength += theRetVal.mRemaining;
				if( str.charAt( nonSpace ) == end ){
					++runningLength;
					theRetVal.mObject = theExpList;
					theRetVal.mRemaining = runningLength;
					theRetVal.mObjectValid = true;
					return theRetVal;
				}
				return Parser.NamedObject.makeDefaultObject( runningLength ); //compile error;			
			}
			nonSpace += theRetVal.mRemaining;
			theExpList.add(  ( InterRep.Designator ) theRetVal.mObject );
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += ( theRetVal.mRemaining + numSpaces );
			while( str.charAt( nonSpace ) == ',' ){
				++nonSpace;
				++runningLength;
				theRetVal = identPatternMatcher( str, nonSpace );
				if( !theRetVal.mObjectValid ) {
					theRetVal.mRemaining = runningLength;
					theRetVal.mObject = theExpList;
					return theRetVal; //this is compile error
				}
				nonSpace += theRetVal.mRemaining;
				numSpaces = stripSpaces( str, nonSpace );
				nonSpace += numSpaces;
				runningLength += ( theRetVal.mRemaining + numSpaces );
				theExpList.add( ( InterRep.Designator  )theRetVal.mObject );
			}
			if( end == str.charAt( nonSpace ) ){
				nonSpace++; runningLength++;
				return new Parser.NamedObject( runningLength, theExpList );
			}
		}
		return Parser.NamedObject.makeDefaultObject( runningLength );
	}
	
	private static Parser.NamedObject functionCallPatternMatcher( String str, int start ) {
		int runningLength = 0;
		Parser.NamedObject retVal = identPatternMatcher( str, start );
		if( retVal.mObjectValid == false )return Parser.NamedObject.makeDefaultObject( retVal.mRemaining );
		String theFunName = ( ( InterRep.Designator ) retVal.mObject ).getMIdentifier();
		runningLength += retVal.mRemaining;
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces + retVal.mRemaining;
		runningLength += numSpaces;
		//check to allow no arguments function to be called without braces arghhhh
		if( nonSpace >= str.length() ){
			InterRep.FunCallStm funCall = new InterRep.FunCallStm( theFunName, new ArrayList< InterRep.Expression > () );
			return new Parser.NamedObject( runningLength, funCall );
		}
		if( str.charAt( nonSpace ) == '(' ){
			Parser.NamedObject argList = expressionCharMatcher( str, nonSpace, '(', ')' );
			runningLength +=  argList.mRemaining;
			ArrayList< InterRep.Expression  > expList = new ArrayList< InterRep.Expression  >();
			if( argList.mObjectValid )
				expList = ( ArrayList< InterRep.Expression  > )argList.mObject;
			InterRep.FunCallStm funCall = new InterRep.FunCallStm( theFunName, expList );
			retVal = new Parser.NamedObject( runningLength, funCall );
			return retVal;
		}
		else{
			InterRep.FunCallStm funCall = new InterRep.FunCallStm( theFunName, new ArrayList< InterRep.Expression > () );
			return new Parser.NamedObject( runningLength, funCall );
		}
		
		//return Parser.NamedObject.makeDefaultObject( runningLength );
	}
	private static Parser.NamedObject factorPatternMatcher( String str, int start ) {
		int runningLength = 0;
		//int 
		int numSpaces = stripSpaces( str, start );
		int nonSpace = numSpaces + start;
		runningLength += numSpaces;
		//sCallMatcher.reset( str );
		if( true == str.startsWith( sCallChar, nonSpace ) ){
			nonSpace += sCallChar.length();
			runningLength += sCallChar.length();
			Parser.NamedObject retVal = functionCallPatternMatcher( str, nonSpace );
			if( retVal.mObjectValid == false ) return Parser.NamedObject.makeDefaultObject( runningLength + retVal.mRemaining );
			InterRep.FunCallWrapper fnWrapper = new InterRep.FunCallWrapper( ( InterRep.FunCallStm ) retVal.mObject );
			runningLength += retVal.mRemaining;
			return new Parser.NamedObject( runningLength, fnWrapper );
			
		}
		else if( '(' == str.charAt( nonSpace ) ){
			Parser.NamedObject theRetVal = expressionCharMatcher( str, nonSpace, '(', ')' );
			if( !theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining );
			nonSpace += theRetVal.mRemaining;
			runningLength += theRetVal.mRemaining;
			ArrayList< InterRep.Expression > theExpList = ( ArrayList< InterRep.Expression> )theRetVal.mObject;
			InterRep.Expression retExp = theExpList.get( 0 );
			
			return new Parser.NamedObject( runningLength, new InterRep.ExpressionWrapper( retExp ) );
				
		}
		else if( isDigit( str, nonSpace) || str.charAt( nonSpace ) == '-' ){
			Parser.NamedObject theRetVal = numPatternMatcher( str, nonSpace );
			if( !theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining );
			runningLength += theRetVal.mRemaining;
			InterRep.Number nmWrapper = new InterRep.Number( ( Integer ) theRetVal.mObject );
			return new Parser.NamedObject( runningLength, nmWrapper );
		}
		else{
			//good old designator or identmatcher
			Parser.NamedObject theRetVal = identPatternMatcher( str, nonSpace );
			if( !theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( theRetVal.mRemaining + runningLength );
			theRetVal.mRemaining += runningLength;
			//InterRep.
			return theRetVal;
		}
		
	}
	private static Parser.NamedObject termPatternMatcher( String str, int start ){
		int runningLength = 0;
		ArrayList< InterRep.Factor > operandsList = new ArrayList< InterRep.Factor >();
		ArrayList< InterRep.BinaryOperations > operatorsList = new ArrayList< InterRep.BinaryOperations >();
		Parser.NamedObject theRetVal = factorPatternMatcher( str, start );
		if( !theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining );
		operandsList.add( ( InterRep.Factor ) theRetVal.mObject );
		start += theRetVal.mRemaining;
		//String termStripped = str.substring( termPos );
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return new Parser.NamedObject( theRetVal.mRemaining, new InterRep.Term( operandsList, operatorsList ) );
		runningLength = ( theRetVal.mRemaining + numSpaces);
		while( str.charAt( nonSpace ) == '*' || str.charAt( nonSpace ) == '/' ){
			if( str.charAt( nonSpace ) == '*' )
				operatorsList.add( InterRep.BinaryOperations.MULTIPLY );
			else
				operatorsList.add( InterRep.BinaryOperations.DIVIDE );			
			++runningLength;++nonSpace;
			theRetVal = factorPatternMatcher( str, nonSpace );
			if(!theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength ); //this is a syntax error??
			operandsList.add( ( InterRep.Factor ) theRetVal.mObject );
			nonSpace += theRetVal.mRemaining;
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += (numSpaces + theRetVal.mRemaining);
			if( nonSpace == str.length() ) return new Parser.NamedObject( runningLength, new InterRep.Term( operandsList, operatorsList ) );
			
		}
		
		return new Parser.NamedObject( runningLength, new InterRep.Term( operandsList, operatorsList ) );
	}
	private static Parser.NamedObject relPatternMatcher( String str, int start ){
		int runningLength = 0;
		InterRep.Expression lhs;
		ArrayList< InterRep.BinaryOperations > operatorsList = new ArrayList< InterRep.BinaryOperations >();
		Parser.NamedObject theRetVal = expPatternMatcher( str, start );
		if( !theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining );
		lhs =  ( InterRep.Expression ) theRetVal.mObject;
		start += theRetVal.mRemaining;
		//runningLength += theRetVal.mRemaining;
		//String termStripped = str.substring( termPos );
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining );
		runningLength = ( theRetVal.mRemaining + numSpaces);
		InterRep.RelationalOperations theRelOp;
		theRelOp = InterRep.returnRelOp( str, nonSpace );
		if( theRelOp != null ){
			if( InterRep.RelationalOperations.GREATERTHAN == theRelOp || InterRep.RelationalOperations.LESSTHAN == theRelOp ){
				nonSpace += 1;
				runningLength += 1;
			}
				
			else{
				nonSpace += 2;
				runningLength += 2;
			}
						
			//++runningLength;++nonSpace;
			InterRep.Expression rhs;
			theRetVal = expPatternMatcher( str, nonSpace );
			if(!theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining ); //this is a syntax error??
			rhs = ( InterRep.Expression ) theRetVal.mObject;
			return new Parser.NamedObject( runningLength + theRetVal.mRemaining, new InterRep.RelationOperation( lhs, rhs, theRelOp ) );
			
		}
		
		return Parser.NamedObject.makeDefaultObject( runningLength );
	}
	private static Parser.NamedObject expPatternMatcher( String str, int start ) {
		int runningLength = 0;
		ArrayList< InterRep.Term > operandsList = new ArrayList< InterRep.Term >();
		ArrayList< InterRep.BinaryOperations > operatorsList = new ArrayList< InterRep.BinaryOperations >();
		Parser.NamedObject theRetVal = termPatternMatcher( str, start );
		if( !theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength + theRetVal.mRemaining );
		operandsList.add( ( InterRep.Term ) theRetVal.mObject );
		start += theRetVal.mRemaining;
		//String termStripped = str.substring( termPos );
		int numSpaces = stripSpaces( str, start );
		int nonSpace = start + numSpaces;
		if( nonSpace == str.length() ) return new Parser.NamedObject( theRetVal.mRemaining, new InterRep.Expression( operandsList, operatorsList ) );
		runningLength = ( theRetVal.mRemaining + numSpaces);
		while( str.charAt( nonSpace ) == '+' || str.charAt( nonSpace ) == '-' ){
			if( str.charAt( nonSpace ) == '+' )
				operatorsList.add( InterRep.BinaryOperations.PLUS );
			else
				operatorsList.add( InterRep.BinaryOperations.MINUS );			
			++runningLength;++nonSpace;
			theRetVal = termPatternMatcher( str, nonSpace );
			if(!theRetVal.mObjectValid ) return Parser.NamedObject.makeDefaultObject( runningLength ); //this is a syntax error??
			operandsList.add( ( InterRep.Term ) theRetVal.mObject );
			nonSpace += theRetVal.mRemaining;
			numSpaces = stripSpaces( str, nonSpace );
			nonSpace += numSpaces;
			runningLength += (numSpaces + theRetVal.mRemaining);
			if( nonSpace == str.length() ) return new Parser.NamedObject( runningLength, new InterRep.Expression( operandsList, operatorsList ) );
			
		}
		
		return new Parser.NamedObject( runningLength, new InterRep.Expression( operandsList, operatorsList ) );
	}
}
}
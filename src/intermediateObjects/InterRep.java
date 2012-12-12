package intermediateObjects;
import java.util.*;
import CodeGen.codegen;
import registerAlloc.*;
//Register Allocation
import optimizer.OPT;
import cfg.cfg.*;
import GraphColoringUtils.graphColoringUtils.DefUseChain;
import GraphColoringUtils.graphColoringUtils.SymbolLocationInfo;
import GraphColoringUtils.graphColoringUtils.Pair;
import GraphColoringUtils.graphColoringUtils.MIRToLIRConvertor;
import GraphColoringUtils.graphColoringUtils.WebBuilder;
import GraphColoringUtils.graphColoringUtils.WebRecord;
import GraphColoringUtils.graphColoringUtils.AdjacencyMatrix;
import GraphColoringUtils.graphColoringUtils.CoalesceSymbolicRegisters;
import GraphColoringUtils.graphColoringUtils.InterferenceGraph;
import GraphColoringUtils.graphColoringUtils.Pair;
public   class InterRep {
	public static enum BinaryOperations {
	    MULTIPLY, DIVIDE, PLUS, MINUS 
	}
	
	public static ArrayList< CodeBlock > BuildCodeBlock( ArrayList< stm > statementsList ) throws Exception {
		ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
		int sz = statementsList.size();
		//CodeBlock prevBlock = null;
		//String labelPrev = null;
		for( int i = 0; i < sz; ++i ){
			ArrayList< CodeBlock > temp = statementsList.get( i ).returnIR();
			retVal.addAll( temp );
			if( i > 0 )
				statementsList.get( i - 1 ).Fixup( temp.get( 0 ).label );
		}
		return retVal;
	}

	public static class SymbolTable{
		private HashMap< String, Boolean > fnOrProc = new HashMap< String, Boolean >();
		public void SetFnOrProc( String fn, boolean isFn ){
			if( !fnOrProc.containsKey( fn ) ){
				fnOrProc.put( fn, isFn );
			}
		}
		public boolean IsFnOrProc( String fn ){
			if( !fnOrProc.containsKey( fn ) ){
				return true;
			}
			else return fnOrProc.get( fn );
		}
		private HashMap< String, VarDecl > fnVarDecls = new HashMap< String, VarDecl >();
		private HashMap< String, ArrayList< String > > fnFnDecls = new HashMap< String, ArrayList< String > >();
		private HashMap< String, ArrayList< String > > fnWhileStms =  new HashMap< String, ArrayList< String > >();
		
		private HashMap<String, Integer> globalVarVsSpillingRegisterLoc = new HashMap<String, Integer>();
		private Integer spillingGlobalRegisterLoc = 0;
		/*private HashMap< String, ArrayList< cfg.cfg.CFGBlock > > resolvedJumpLabelMap = new HashMap< String, ArrayList< cfg.cfg.CFGBlock > >();
		public void AddJumpLabel( String label, ArrayList< cfg.cfg.CFGBlock > theCFGBlocks ){
			if( resolvedJumpLabelMap.containsKey( label ) ){
				resolvedJumpLabelMap.get( label ).addAll( theCFGBlocks );
				return;
			}
			ArrayList< cfg.cfg.CFGBlock > theBlocks = new ArrayList< cfg.cfg.CFGBlock >();
			theBlocks.addAll( theCFGBlocks );
			resolvedJumpLabelMap.put( label, theBlocks );
		}
		
		public void ReplaceJumpLabel( String from, cfg.cfg.CFGBlock currentBlock ){
			String newLabel = currentBlock.BlockLabel();
			if( !resolvedJumpLabelMap.containsKey( from ) )return;
			ArrayList< cfg.cfg.CFGBlock > cfgs = resolvedJumpLabelMap.remove( from  );
			for( cfg.cfg.CFGBlock theBlk : cfgs ){
				theBlk.ReplaceJumpLabelTo( newLabel );
			}
			resolvedJumpLabelMap.put( newLabel, cfgs );
		} 
		
		public Set< String > returnJumpLabels(){
			return resolvedJumpLabelMap.keySet();
		}
		*/
		private String currentContext = new String();
		private VarDecl curVarDecl = new VarDecl();
		private VarDecl globalVarDecl = null;
		private void EnsureGlobalsExist(){
			if( null != globalVarDecl ) return;
			globalVarDecl = this.fnVarDecls.get("main");
		}
		private HashSet< String > rejected = new HashSet< String >(); //the ones main could safely optimize
		private String optScope = null;
		public void SetOptimizeScope( String curScope ){
			optScope = curScope;
		}
		
		public String GetOptimizeScope(){
			return optScope;
		}
		public void ResetOptimizeScope(){
			optScope = null;
		}
		
		public void AddToRejectListForMain( String varname ){
			if( varname.equals("y")){
				boolean a = true;
			}
			if( optScope.equals( "main" ) ) return;
			
			if( this.isGlobal( varname ) ){
				rejected.add( varname );
			}
		}
		
		public boolean IsSafeForOptimize( CodeBlock cdBlk ){
			String curVar = cdBlk.outputTemporary.serializeMe();
			boolean isGlb = this.isGlobal( curVar );
			if( isGlb && optScope.equals("main") && !rejected.contains(curVar ) ) return true;
			else if( isGlb && optScope.equals("main") )return false;
			else if( isGlb && !optScope.equals("main") ) return false;
			return true;
		}
		public void Init(){
			this.currentContext = "InputNum";
			VarDecl vdIN = new VarDecl( new ArrayList< String >(), new Hashtable< String, ArrayList< Integer > >() );
			fnVarDecls.put( "InputNum", vdIN );
			//this.setReturnInfo
			this.currentContext = "OutputNum";
			VarDecl vdON = new VarDecl( new ArrayList< String >(), new Hashtable< String, ArrayList< Integer > >() );
			ArrayList< String > fmls = new ArrayList< String >();
			fmls.add( "x" );
			vdON.AddFormals( fmls );
			fnVarDecls.put( "OutputNum", vdON );
			this.currentContext = "OutputNewLine";
			VarDecl vdONL = new VarDecl( new ArrayList< String >(), new Hashtable< String, ArrayList< Integer > >() );
			fnVarDecls.put( "OutputNewLine", vdONL );
			this.currentContext = new String();
		}
		public  ArrayList< String > getDeclListCurrent (){
			return curVarDecl.getMIdentList();
		}
		
		public boolean isGlobal( String identifier ){
			EnsureGlobalsExist();
			if( identifier.equals("n")){
				boolean a = true;
			}
			return globalVarDecl.mAddressInfo.get( identifier ) != null;
		}
		
		public boolean isGlobalFun( String funName ){
			return funName.equals("OutputNewLine") || funName.equals("InputNum") || funName.equals("OutputNum");
		}
		public Integer getGlobalRegisterSpillingLoc(String identifier){
			if(globalVarVsSpillingRegisterLoc.containsKey(identifier)){
				return globalVarVsSpillingRegisterLoc.get(identifier);
			}
			globalVarVsSpillingRegisterLoc.put(identifier, spillingGlobalRegisterLoc);
			System.out.println("Global Variable: "+identifier+" - Loc: G"+ spillingGlobalRegisterLoc);
			spillingGlobalRegisterLoc++;
			return globalVarVsSpillingRegisterLoc.get(identifier);
		}
		public VarDecl getVarDeclInfo( String funcName ){
			return fnVarDecls.get( funcName );
		}
		public void setReturnInfo( String retAddress, String funcName ) throws Exception {
			if( !this.fnVarDecls.containsKey( funcName ) )
				throw new Exception("Function activation record not found");
			fnVarDecls.get( funcName ).mReturnInfo = this.generateNewFrameInfo(funcName + "$RETURN");
			fnVarDecls.get(funcName ).mReturnAddress = retAddress;
		}
		
		public ArrayList< String > getWhileLabels( String funcName ){
			if( fnWhileStms.containsKey( funcName ) )
				return fnWhileStms.get( funcName  );
			
			return new ArrayList< String >();
		}
		
		public void ReplaceKey( String key1, String key2, FrameInfo fm ){
			if( fm.tempID.equals( key1 ) ) fm.ssaName = new String(key2);
			//this.curVarDecl.ReplaceKey( key1, key2 );
		}
		public String variableName( FrameInfo var ){
			return var.tempID;
		}
		public void AddWhileStm( String label ){
			if( fnWhileStms.containsKey( currentContext) ){
				fnWhileStms.get( currentContext ).add( label );
				return;
			}
			ArrayList< String > temp = new ArrayList< String >();
			temp.add( label );
			fnWhileStms.put( currentContext, temp );
		}
		public void SetCurrentContext( String funcName ) throws Exception {
			if( fnVarDecls.containsKey( funcName ) == true )
				curVarDecl = fnVarDecls.get( funcName );
			currentContext = funcName;
		}	
		public String getCurrentContext() {
			return currentContext;
		}
		
		public String getLValueTemporary( String identifier ) throws Exception {
			FrameInfo fm = curVarDecl.mAddressInfo.get( identifier  );
			if( null == fm )
				throw new Exception( "Undefined identifier:" + identifier );
			return fm.returnLValueTemporary();
		}
		
		public String getRValueTemporary( String identifier ) throws Exception {
			FrameInfo fm = curVarDecl.mAddressInfo.get( identifier  );
			if( null == fm )
				throw new Exception( "Undefined identifier:" + identifier );
			return fm.returnRValueTemporary();
		}
		
		public FrameInfo getAddressInfo( String identifier )  throws Exception {
			FrameInfo fm = curVarDecl.mAddressInfo.get( identifier  );
			if( null == fm ){
				if( null == globalVarDecl ){
					globalVarDecl = this.getVarDeclInfo( "main" );
					if( null == globalVarDecl ) return null;
				}
				fm = globalVarDecl.mAddressInfo.get( identifier );
				return fm;
			}
				
			return fm;
		}
		
		public FrameInfo getReturnValue( String funcName ) {
			if( !this.fnVarDecls.containsKey( funcName ) )
				return null;
			if( fnVarDecls.get( funcName ).mReturnInfo.tempID.isEmpty() )
				fnVarDecls.get( funcName ).mReturnInfo = this.generateNewFrameInfo(funcName + "$RETURN");
			return fnVarDecls.get( funcName ).mReturnInfo;
		}
		
		public String getReturnAddressLabel( String funcName ) throws Exception {
			if( !this.fnVarDecls.containsKey( funcName ) )
				throw new Exception("Function activation record not found");
			
			return fnVarDecls.get( funcName ).mReturnAddress;
		}
		
		public FrameInfo generateConstantFrameInfo( Integer number ){
			ConstFrameInfo locInfo = new ConstFrameInfo();
			//locInfo.isTemporary = true;
			locInfo.framePtr = 0;
			locInfo.frameOffset = 0;
			locInfo.tempID = String.valueOf( number );
			locInfo.frameName = globalSymTab.getCurrentContext();
			locInfo.constVal = number;
			return locInfo;
		}
		
		public ArrayList< String > identList( ArrayList< Designator > desig ){
			ArrayList< String > strList = new ArrayList< String >();
			int sz = desig.size();
			for( int i = 0; i < sz; ++i ){
				strList.add( desig.get( i ).getMIdentifier() );
			}
			return strList;
		}
		public FrameInfo generateNewFrameInfo( String identifier ){
			LocationInfo locInfo = new LocationInfo();
			locInfo.isTemporary = true;
			locInfo.framePtr = 0;
			locInfo.frameOffset = 0;
			locInfo.tempID =  identifier;
			locInfo.frameName = globalSymTab.getCurrentContext();
			return locInfo;
		}
		
		public ArrayList< FrameInfo > getFormalsInfo( String funcName ) {
			if( !this.fnVarDecls.containsKey( funcName ) )
				throw new Error("Function activation record not found");
			
			return fnVarDecls.get( funcName ).mFormalParamsInfo;
		}
		
		public void AddContextVars( String fnName, VarDecl vdc ){
			fnVarDecls.put( fnName, vdc );
		}
	}
	public static SymbolTable globalSymTab = new SymbolTable();
	public static class LabelMaker{
		private static Integer labelCounter = 0;
		public String newLabel( ){
			String curFun = globalSymTab.getCurrentContext();
			String retVal = new String();
			++labelCounter;
			retVal = curFun + ":" + String.valueOf( labelCounter );
			return retVal;
		}
	}
	public static LabelMaker globalLabelMaker = new LabelMaker();
	public static class CodeBlock{
		public int fnIndex = 0;
		public Boolean isLetMoveStatement = false;
		public Boolean isGlobalAssignment = false;
		public Boolean isArgPassingStatement = false;
		public boolean isSpillIns = false;
		public boolean somethingChanged = false; //java doesnt offer pass by ref
		public Boolean isDeleted = false;
		public ArrayList< CodeBlock > prologue = new ArrayList< CodeBlock > (); //phiblocks or prologue in case of func block
		public String label = new String();
		public int opCode = -1;
		public ArrayList< FrameInfo > operands = new ArrayList< FrameInfo >(); //because of phi we need to have arraylist of operands rather than 2 operands.
		public FrameInfo outputTemporary = new LocationInfo();
		private String canonicalName = null;
		public String jumpLabel = new String();
		public Boolean isCall = false;
		public Boolean isReturn = false;
		public ArrayList< CodeBlock > epilogue = new ArrayList< CodeBlock >(); //in case of return statement
		public String movCanonicalName = null;
		public ArrayList< String > rvalOperands = null;
		private boolean IsExpression() {
			return this.opCode < this.kLOAD;
		}
		
		//Sad really.
		public void ResetCache(){
			movCanonicalName = null;
			canonicalName = null;
			rvalOperands = null;
		}
		public boolean IsConstantCompare(){
			return opCode == CodeBlock.kCMP && ( ( operands.get( 0 ) instanceof ConstFrameInfo && operands.get( 1 ) instanceof ConstFrameInfo )
					|| operands.get( 0 ).serializeMe().equals( operands.get( 1 ).serializeMe() ) );
		}
		public boolean IsCondBra(){
			return CodeBlock.kBNE <= opCode && opCode <= CodeBlock.kBGT;
		}
		public boolean PerformComparison( CodeBlock condBra ){
			Integer val1;
			Integer val2;
			if( operands.get( 0 ).serializeMe().equals( operands.get( 1 ).serializeMe() ) ){
				val1 = 1;
				val2 = 1;
			} 
			else if(  ( operands.get( 0 ) instanceof ConstFrameInfo && operands.get( 1 ) instanceof ConstFrameInfo ) ){
				val1 = Integer.valueOf( operands.get( 0 ).serializeMe() );
				val2 = Integer.valueOf( operands.get( 1 ).serializeMe() );
			}
			else{
				return false;
			}
			boolean taken = false;
			switch( condBra.opCode ){
			case CodeBlock.kBNE:
				taken = val1 != val2;
				break;
			case CodeBlock.kBEQ:
				taken = val1 == val2;
				break;
			case CodeBlock.kBLE:
				taken = val1 <= val2;
				break;
			case CodeBlock.kBLT:
				taken = val1 < val2;
				break;
			case CodeBlock.kBGE:
				taken = val1 >= val2;
				break;
			case CodeBlock.kBGT:
				taken = val1 > val2;
				break;
			}
			return taken;
		}
		public void ProcessOperandsForMain(){
			for( FrameInfo fm : operands ){
				String curVar = fm.serializeMe();
				globalSymTab.AddToRejectListForMain( curVar );
				if( opCode == kMOVE ) break;
			}
			if( outputTemporary != null ){
				String op = outputTemporary.serializeMe();
				globalSymTab.AddToRejectListForMain( op );
			}
		}
		public boolean IsGlobalAssignment(){
			return IsMove() && isGlobalAssignment;
		}
		
		private boolean IsMove(){
			return this.opCode == this.kPHI || this.opCode == this.kMOVE;
		}
		public String returnMovCanonicalName(){
			if( null != movCanonicalName || !IsMove() ) return movCanonicalName;
			movCanonicalName = new String();
			for( FrameInfo fm : this.operands ){
				movCanonicalName += fm.serializeMe() + "|";
				if( this.opCode == kMOVE ) break;
			}
			movCanonicalName += this.outputTemporary.serializeMe();
			return movCanonicalName;
			
		}
		private boolean IsBinaryOperation(){
			return opCode == CodeBlock.kADD || opCode == CodeBlock.kSUB || opCode == CodeBlock.kMUL || opCode == CodeBlock.kDIV;
		}
		
		private FrameInfo EvaluateBinOp(){
			if( !IsBinaryOperation() ) return null;
			if( !(operands.get( 0 ) instanceof ConstFrameInfo) || !(operands.get( 1 ) instanceof ConstFrameInfo)  ) return null;
			Integer val1 = Integer.valueOf( operands.get( 0 ).serializeMe() );
			Integer val2 = Integer.valueOf( operands.get( 1 ).serializeMe() );
			Integer val3 = 0;
			switch( opCode ){
			case kADD:
				val3 = val1 + val2;
				break;
			case CodeBlock.kSUB:
				val3 = val1 - val2;
				break;
			case CodeBlock.kMUL:
				val3 = val1 * val2;
				break;
			case CodeBlock.kDIV:
				val3 = val1 / val2;
				break;
			}
			//String valTemp = String.valueOf( val3 );
			FrameInfo fm = globalSymTab.generateConstantFrameInfo( val3 );
			return fm;
		} 
		public boolean IsReturnOp(){
			if( opCode != CodeBlock.kMOVE ) return false;
			return this.outputTemporary.serializeMe().contains("$RETURN");
		}
		public CodeBlock EvaluateOperandsIfConstant( ){
			CodeBlock moveBlock = null;
			if( !IsBinaryOperation() ) return moveBlock;
			FrameInfo fm = EvaluateBinOp();
			if( null == fm ) return moveBlock;
			moveBlock = CodeBlock.generateMoveNumber( Integer.valueOf( fm.serializeMe() ) );
			moveBlock.outputTemporary = this.outputTemporary.Clone();
			moveBlock.label = new String( this.label );
			return moveBlock;
		}
		private boolean IsOperandValid( FrameInfo fm, HashMap< String, String > ignoreList ){
			String opName = fm.returnRValueTemporary();
			String opVal = fm.serializeMe();
			if( null == opName || opName.isEmpty() || !ignoreList.containsKey( opName ) )return true; //must be a temporary used to store temp calculations.
			String value = ignoreList.get( opName );
			return value.equals( opVal ); //if !equals definition is killed before this context, else definition reaches this context so copy maybe propagated
		}
		public boolean ReplaceMovOperands( HashMap< String, FrameInfo > replacements, HashMap< String, String > ignoreList ){
			if( this.isDeleted || this.opCode != kMOVE ) return false;
			String curOp = this.operands.get( 0 ).serializeMe();
			String origName = this.operands.get( 0 ).returnRValueTemporary();
			FrameInfo finalVal = null;
			String temp = null;
			while(( finalVal = replacements.get( curOp ) ) != null  ){
				temp = curOp;
				curOp = finalVal.serializeMe();
			}
			if( null != temp ){
				finalVal = replacements.get( temp );
				if( IsOperandValid( finalVal, ignoreList ) ){
					this.operands.set( 0, finalVal.Clone() );
					somethingChanged = true;
				}
				return true;
			}
			
			return false;
		}
		public boolean ReplaceOperands( HashMap< String, FrameInfo >  replacements, HashMap< String, String > ignoreList ){
			if( this.isDeleted ) return false;
			ArrayList< String > rvals = returnRVALOperands();
			if( null == rvals ) return false;
			String lastOp = null;
			boolean isEqual = true;
			for( int i = 0; i < rvals.size(); ++i ){
				FrameInfo finalVal = null;
				//FrameInfo lastFinalVal = null;
				String curOp = rvals.get( i );
				String temp = null;
				while( ( finalVal = replacements.get( curOp ) ) != null ){
					temp = curOp;
					curOp = finalVal.serializeMe();
				}
				
				if( null != temp ){
					 finalVal = replacements.get( temp );
					if( IsOperandValid( finalVal, ignoreList ) ){
						curOp = temp;
						this.operands.set( i , finalVal.Clone() );
						somethingChanged = true;
					}
					else{
						curOp = this.operands.get( i ).serializeMe();
					}
				}
				if( lastOp != null ) isEqual = isEqual && (curOp.equals( lastOp ) );
				lastOp = curOp;
			}
			return isEqual;
		}
		
		public void ReplaceOperand( HashMap< String, FrameInfo > replacements, int i, HashMap< String, String > ignoreList ){
			if( this.isDeleted ) return;
			String curOp = this.operands.get( i ).serializeMe();
			String temp = null;
			FrameInfo finalVal = null;
			FrameInfo lastFinalVal = null;
			while( ( finalVal = replacements.get( curOp ) ) != null  ){
				temp = curOp;
				curOp = finalVal.serializeMe();
				lastFinalVal = finalVal;
			}
			
			if( null != lastFinalVal && IsOperandValid( lastFinalVal, ignoreList ) ) {
				this.operands.set( i, lastFinalVal.Clone() );
				somethingChanged = true;
			}
		}
		
		public boolean AllOperandsSame(){
			boolean isEqual = true;
			String lastOp = null;
			for( FrameInfo fm : this.operands ){
				String curOp = fm.serializeMe();
				if( null != lastOp ){
					isEqual = isEqual && curOp.equals( lastOp );
				}
				lastOp = curOp;
			}
			return isEqual;
		}
		
		public FrameInfo PhiAllButOneSame(){
			if( opCode != kPHI ) return null;
			String op = this.outputTemporary.serializeMe();
			int cnt = 0;
			FrameInfo differing = null;
			for( FrameInfo fm : this.operands ){
				String curOp = fm.serializeMe();
				if( !curOp.equals( op ) ){
					++cnt;
					if( 1 < cnt ){
						differing = null;
					}
					else if( 1 == cnt ){
						differing = fm;
					}
				}
			}
			return differing;
		}
		public ArrayList< String > returnRVALOperands(){
			if( null != rvalOperands ) return rvalOperands;
			rvalOperands = new ArrayList< String >();
			for( FrameInfo fm : this.operands ){
				rvalOperands.add( fm.serializeMe() );
				if( this.opCode == kMOVE ) break;
			}
			return rvalOperands;
		}
		
		public String returnLVALOperand(){
			return this.outputTemporary.serializeMe();
		}
		
		public FrameInfo returnMovOperand(){
			return this.operands.get( 0 );
		}
		
		public void SubstituteOperand( int j, FrameInfo fm ){
			this.operands.set( j, fm.Clone() );
		}
		
		public String returnCanonicalName(){
			if( null != canonicalName || !IsExpression() ) return canonicalName;
			
			canonicalName = new String();
			for( FrameInfo fm : this.operands ){
				canonicalName += fm.serializeMe() + "|";
			}
			canonicalName += String.valueOf( this.opCode );
			//saala goli marna chahiye
			/*switch( opCode ){
			case kADD:
			case kMUL:
			case kADDA:{
				 char[] content = canonicalName.toCharArray();
				 java.util.Arrays.sort(content);
				 canonicalName = new String( content );
			}
			
			}*/
			return canonicalName;
		}
		public  CodeBlock Clone(){
			CodeBlock cloned = new CodeBlock();
			cloned.fnIndex = this.fnIndex;
			cloned.isReturn = this.isReturn;
			cloned.isArgPassingStatement = this.isArgPassingStatement;
			cloned.isSpillIns = this.isSpillIns;
			cloned.isCall = this.isCall;
			cloned.isDeleted = this.isDeleted;
			cloned.isLetMoveStatement = this.isLetMoveStatement;
			cloned.prologue = new ArrayList< CodeBlock >();
			cloned.canonicalName = this.canonicalName;
			cloned.movCanonicalName = this.movCanonicalName;
			cloned.isGlobalAssignment = this.isGlobalAssignment;
			cloned.somethingChanged = this.somethingChanged;
			for( CodeBlock cs : this.prologue ){
				cloned.prologue.add( cs.Clone() );
			}
			cloned.epilogue = new ArrayList< CodeBlock >();
			for( CodeBlock cs : this.epilogue ){
				cloned.epilogue.add( cs.Clone() );
			}
			
			cloned.label = new String( this.label );
			cloned.jumpLabel = new String( this.jumpLabel );
			cloned.opCode = this.opCode;
			cloned.operands = new ArrayList< FrameInfo >();
			for( FrameInfo fm : this.operands ){
				cloned.operands.add( fm.Clone() );
			}
			if (null != outputTemporary) {
				cloned.outputTemporary = this.outputTemporary.Clone();
			} else {
				cloned.outputTemporary = null;
			}
			
			return cloned;
		}
		public static final String[] translation = {
			"neg", "add", "sub", "mul", "div",
			"cmp", "adda", "load", "store", "move",
			"phi", "bra", "bne", "beq", "ble", "blt",
			"bge", "bgt", "read", "write", "wln"
		};
		public static String serializeMe( CodeBlock cs ){
			String s = new String();
			if( cs.isDeleted )return s;
			s += cs.label + " : ";
			if( cs.isCall ){
				s += " call " + cs.jumpLabel + "(";
			} else if( cs.isReturn ){
				s += " ret\n ";
				return s;
			} else {
				s += translation[ cs.opCode ];
			}
			int sz = cs.operands.size();
			for( int i = 0; i < sz; ++ i ){
				s += " ";
				s += cs.operands.get( i ).serializeMe();
				if( cs.opCode == kMOVE ) break;
				if (cs.isCall && i + 1 < sz) {
					s += ",";
				}
			}
			if (cs.isCall) {
				s += ")";
			}
			s += " ";
			if( kBRA <= cs.opCode && cs.opCode <= kBGT  && !cs.isCall){
				s += cs.jumpLabel;
				s += " ";
			}
			if (!cs.isCall && null != cs.outputTemporary) {
				s += " ";
				s += cs.outputTemporary.serializeMe();
			}
			s += ",\n";
			return s;
		}
		
		public static final int kNEG = 0;
		public static final int kADD = 1;
		public static final int kSUB = 2;
		public static final int kMUL = 3;
		public static final int kDIV = 4;
		public static final int kCMP = 5;
		public static final int kADDA = 6;
		public static final int kLOAD = 7;
		public static final int kSTORE = 8;
		public static final int kMOVE = 9;
		public static final int kPHI = 10;
		public static final int kBRA = 11;
		public static final int kBNE = 12;
		public static final int kBEQ = 13;
		public static final int kBLE = 14;
		public static final int kBLT = 15;
		public static final int kBGE = 16;
		public static final int kBGT = 17;
		
		public static final int kREAD = 18;
		public static final int kWRITE = 19;
		public static final int kWLN = 20;
		
		public static int TranslateBinOpToOpcode( BinaryOperations theOp ){
			if( BinaryOperations.PLUS == theOp )
				return kADD;
			if( BinaryOperations.MINUS == theOp )
				return kSUB;
			if( BinaryOperations.MULTIPLY == theOp )
				return kMUL;
			if( BinaryOperations.DIVIDE == theOp )
				return kDIV;
			return -1;
		}
		
		public static int InvertRelOp( InterRep.RelationalOperations theRelOp ){
			if( RelationalOperations.EQUALITY == theRelOp )
				return CodeBlock.kBNE;
			if( RelationalOperations.NONEQUALITY == theRelOp )
				return CodeBlock.kBEQ;
			if( RelationalOperations.GREATERTHAN == theRelOp )
				return CodeBlock.kBLE;
			if( RelationalOperations.GREATERTHANEQUALS == theRelOp )
				return CodeBlock.kBLT;
			if( RelationalOperations.LESSTHAN == theRelOp )
				return CodeBlock.kBGE;
			if( RelationalOperations.LESSTHANEQUALS == theRelOp )
				return CodeBlock.kBGT;
			return -1;
		}
		
		public static CodeBlock generatePhiBlock( String var, Integer pred ) throws Exception {
			CodeBlock cd = new CodeBlock();
			cd.opCode = CodeBlock.kPHI;
			FrameInfo fm = globalSymTab.getAddressInfo( var );
			if( null == fm )
				fm = globalSymTab.generateNewFrameInfo( var );
			for( int i = 0; i < pred; ++i) {
				cd.operands.add( fm.Clone() );
			}
			cd.label = globalLabelMaker.newLabel();
			cd.outputTemporary = fm.Clone();
			cd.isLetMoveStatement = true;
			return cd;
		}
		public static CodeBlock generateMoveNumber( Integer number ){
			FrameInfo rval = globalSymTab.generateConstantFrameInfo( number );
			CodeBlock moveConstBlock = new CodeBlock();
			moveConstBlock.opCode = CodeBlock.kMOVE;
			moveConstBlock.operands.add( rval );
			moveConstBlock.label = globalLabelMaker.newLabel();
			moveConstBlock.outputTemporary = globalSymTab.generateNewFrameInfo( moveConstBlock.label );
			//moveConstBlock.operands.add( )
			return moveConstBlock;
		}
		
		public static CodeBlock generateUnCondBranch( ){
			//Labels and whether call or return prolog and epilog will all be added by the caller.
			CodeBlock unCondJmp = new CodeBlock();
			unCondJmp.opCode = CodeBlock.kBRA;
			unCondJmp.label = globalLabelMaker.newLabel();
			return unCondJmp;
		}
		
		public static CodeBlock generateBinOP( FrameInfo x, FrameInfo y, Integer inOpCode ) {
			CodeBlock mulCodeBlock = new CodeBlock();
			mulCodeBlock.opCode = inOpCode;
			mulCodeBlock.operands.add( x );
			mulCodeBlock.operands.add( y );
			mulCodeBlock.label = globalLabelMaker.newLabel();
			mulCodeBlock.outputTemporary = globalSymTab.generateNewFrameInfo( mulCodeBlock.label );
			return mulCodeBlock;
		}
		
		public static CodeBlock generateUnOP( FrameInfo x, Integer inOpCode ){
			CodeBlock mulCodeBlock = new CodeBlock();
			mulCodeBlock.opCode = inOpCode;
			mulCodeBlock.operands.add( x );
			mulCodeBlock.label = globalLabelMaker.newLabel();
			mulCodeBlock.outputTemporary = globalSymTab.generateNewFrameInfo( mulCodeBlock.label );
			return mulCodeBlock;
		}
		
		public static CodeBlock generateMoveOrStoreOP( FrameInfo y, FrameInfo x, Integer inOpCode ){
			CodeBlock mulCodeBlock = new CodeBlock();
			mulCodeBlock.opCode = inOpCode;
			mulCodeBlock.operands.add( y );
			mulCodeBlock.operands.add( x );
			mulCodeBlock.label = globalLabelMaker.newLabel();
			if( inOpCode == CodeBlock.kMOVE )
				mulCodeBlock.outputTemporary = x;
			
			return mulCodeBlock;
		}
		
		public static ArrayList< CodeBlock > generateInvertedRelOPJump( FrameInfo lval, FrameInfo rval, InterRep.RelationalOperations theRelOp ){
			//we dont do fixup here statements are supposed to.
			ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
			int opCode = CodeBlock.InvertRelOp( theRelOp );
			
			CodeBlock cmpBlock = CodeBlock.generateBinOP( lval, rval, CodeBlock.kCMP );
			FrameInfo opTemp = cmpBlock.outputTemporary;
			retVal.add( cmpBlock );
			
			//LOGIC: we are simply reusing generate unOp to generate branches, the second op which is the label will be fixed up later.
			CodeBlock brBlock = CodeBlock.generateUnOP( opTemp, opCode );
			retVal.add( brBlock );
			return retVal;
			
		}
	}
	public static class CodeTree{
		private HashMap< String, ArrayList< CodeBlock > > fnCode = new HashMap< String, ArrayList< CodeBlock > >();
		public void AddCodeBlock( String fn, ArrayList< CodeBlock > code ) throws Exception{
			globalSymTab.SetOptimizeScope( fn );
			fnCode.put( fn, code );
			cfg.cfg.CFGBlock theRoot = cfg.cfg.BuildCFGBlock( fn, code );
			{
				cfg.cfg.Dominator.DumpToVCG( fn + "ControlFlowGraph.vcg", theRoot, 0, null );
			}
			
			cfg.cfg.Dominator domTreeBuilder = new cfg.cfg.Dominator();
			theRoot = domTreeBuilder.BuildDominatorTree( theRoot );
			{
				cfg.cfg.Dominator.DumpToVCG( fn + "Dominator.vcg", theRoot, 1, null );
			}
			
			theRoot = domTreeBuilder.BuildDominanceFrontier(theRoot );
			{
				cfg.cfg.Dominator.DumpToVCG( fn + "DominanceFrontier.vcg", theRoot, 2, domTreeBuilder );
			}
			
		//	cfg.cfg.Dominator.DumpToVCG( "ControlFlowGraph.vcg", theRoot );
			theRoot = domTreeBuilder.InsertPhiFuncBlock( );
			{
				cfg.cfg.Dominator.DumpToVCG( fn + "PhiBlock.vcg", theRoot, 0, null );
			}
			domTreeBuilder.InitializeForRenaming();
			cfg.cfg.OPTParamBlock paramBlock = domTreeBuilder.RenamePhiBlock( theRoot );
			{
				cfg.cfg.Dominator.DumpToVCG( fn + "Renamed.vcg", paramBlock.root, 0, null );
			}
		
			boolean somethingChanged = false;
			int counter = 2;
			do{
				optimizer.OPT.CopyPropagation copyProp = new optimizer.OPT.CopyPropagation( paramBlock );
				copyProp.Optimize( paramBlock.root );
				{
					cfg.cfg.Dominator.DumpToVCG( fn + "CopyProp"  +  String.valueOf( counter ) + ".vcg" , paramBlock.root, 0, null );
				}
				optimizer.OPT.CommonSubexpressionElimination commonSubExp = new optimizer.OPT.CommonSubexpressionElimination( paramBlock );
				commonSubExp.Optimize( paramBlock.root );
				{
					cfg.cfg.Dominator.DumpToVCG( fn + "CommonSubExp" +  String.valueOf( counter ) + ".vcg" , paramBlock.root, 0, null );
				}
				somethingChanged = commonSubExp.didSomethingChange();
				if( !somethingChanged ) break;
				//counter--;
			}while( counter-- >= 0 );
			if( somethingChanged ){
				optimizer.OPT.CopyPropagation copyProp = new optimizer.OPT.CopyPropagation( paramBlock );
				copyProp.Optimize( paramBlock.root );
				{
					cfg.cfg.Dominator.DumpToVCG( fn + "CopyProp"  +  String.valueOf( counter ) + ".vcg" , paramBlock.root, 0, null );
				}
			}
			for( CFGBlock cfgb : paramBlock.vertex ){
				String lbl = cfgb.BlockLabel();
				if( lbl.equals( "main:112" ) ){
					boolean a = true;
				}
			}
			/*//Register Allocation
			RegisterAllocator regAllocate = new RegisterAllocator();
			regAllocate.BuildRegAllocUsingLinearScan(theRoot);
			cfg.cfg.Dominator.DumpToVCG( fn + "AfterRegAlloc.vcg", theRoot, 0, null );
			//fix for crash in test018.txt due to register allocator adding an extra instruction in the front of a cfg block
			for( CFGBlock cfgb : paramBlock.vertex ){
				String lbl = cfgb.BlockLabel();
				if( lbl.equals( "main:112" ) ){
					boolean a = true;
				}
			}
			//initialize codegen phase here 
			codegen.PreProcess( fn, paramBlock );*/
			boolean success = false;
			List<CFGBlock> inputBlocks = paramBlock.vertex;
			AdjacencyMatrix adjMatrix = null;
			List<CFGBlock> coalescedLirBlocks = null;
			boolean firstTime = true;
			do {
				success = false;
				DefUseChain defUseChainBuilder = new DefUseChain();
				final Map<Pair<String, SymbolLocationInfo>, ArrayList<SymbolLocationInfo>> duChain =
					defUseChainBuilder.buildDefUseChain(inputBlocks);
				
				final WebBuilder buildWebs = new WebBuilder ();
				final Set<WebRecord> webRecords = buildWebs.makeWeb(duChain);
				
				List<CFGBlock> lirBlocks = null;
				final MIRToLIRConvertor lirConvertor = new MIRToLIRConvertor ();
				
				lirBlocks = lirConvertor.buildLIRFromMIR(inputBlocks, webRecords);
				{
					cfg.cfg.Dominator.DumpToVCG( fn + "LirCode"  +  ".vcg" , lirBlocks.get(0), 0, null );
				}
				final AdjacencyMatrix adjacentMatrix = new AdjacencyMatrix (lirBlocks);
				adjacentMatrix.buildAdjacencyMatrix();
				adjMatrix = adjacentMatrix;
				final String output = adjacentMatrix.serializeGraphToString();
				System.out.println(output);
				
				final CoalesceSymbolicRegisters registerCoalescer 
				= new CoalesceSymbolicRegisters(adjacentMatrix, lirBlocks);
				
				Pair<List<CFGBlock>, Boolean> coalescedLirBlocksPair = registerCoalescer.coalesceRegisters();
				coalescedLirBlocks = coalescedLirBlocksPair.getFirst();
				{
					cfg.cfg.Dominator.DumpToVCG( fn + "coalescedLirCode"  +  ".vcg" , coalescedLirBlocks.get(0), 0, null );
				}
				

				
				final InterferenceGraph interferenceGraph =
					new InterferenceGraph (adjMatrix);
				System.out.println (interferenceGraph.toString());
				interferenceGraph.buildSpillCostFromCodeBlocks(coalescedLirBlocks);
				interferenceGraph.pruneGraph();
				success = interferenceGraph.assignRegisters();
				if (success) {
					coalescedLirBlocks = interferenceGraph.modifyCode(coalescedLirBlocks);
				} else {
					coalescedLirBlocks = interferenceGraph.genSpillCode(coalescedLirBlocks);
				}
				{
					cfg.cfg.Dominator.DumpToVCG( fn + "registerAlloc"  +  ".vcg" , coalescedLirBlocks.get(0), 0, null );
				}
				inputBlocks = coalescedLirBlocks;
			} while (!success);
			
			globalSymTab.ResetOptimizeScope();
		}
	}

	public static CodeTree gCodeTree = new CodeTree();
	public static String serializeBinaryOpn( BinaryOperations val ){
		switch( val ){
		case MULTIPLY:
			return "multiply";
		case DIVIDE:
			return "divide";
		case PLUS:
			return "add";
		case MINUS:
			return "subtract";
		}
		return "";
	}
	public static enum RelationalOperations {
		GREATERTHAN, LESSTHAN, EQUALITY, NONEQUALITY, 
		LESSTHANEQUALS, GREATERTHANEQUALS
	}
	
	public static RelationalOperations returnRelOp( String str, int nonSpace ){
		if( str.startsWith( "==",  nonSpace ) )
			return RelationalOperations.EQUALITY;
		if( str.startsWith( "!=",  nonSpace ) )
			return RelationalOperations.NONEQUALITY;
		if( str.startsWith( "<=",  nonSpace ) )
			return RelationalOperations.LESSTHANEQUALS;
		
		if( str.startsWith( ">=",  nonSpace ) )
			return RelationalOperations.GREATERTHANEQUALS;
		if( str.startsWith( ">",  nonSpace ) )
			return RelationalOperations.GREATERTHAN;
		if( str.startsWith( "<",  nonSpace ) )
			return RelationalOperations.LESSTHAN;
				
		return null;	
		
	}
public static abstract class stm{
	abstract String opCode();
	public void  Fixup( String e ) throws Exception{
		
	}
	abstract public ArrayList< CodeBlock > returnIR() throws Exception;
	
	abstract public FrameInfo returnOutputTemp() throws Exception;
	
}

public static class ExpressionStm extends stm{
	private Expression mExpression = null;
	public String opCode(){
		return mExpression.opCode();
	}
	public ExpressionStm( Expression exp ){
		super();
		mExpression = exp;
	}
	public ArrayList< CodeBlock > returnIR() throws Exception{
		return mExpression.returnIR();
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		return mExpression.returnOutputTemp();
	}
	
	public void Fixup( String e ) throws Exception{
		mExpression.Fixup( e );
	}
}
public  static class Designator extends Factor{
	private String mIdentifier;
	private ArrayList< Expression > mExpression;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	private ArrayList< CodeBlock > mLRetVal = new ArrayList< CodeBlock >();
	private Expression mLastAssignedExp = null;
	private FrameInfo getAddressInfo( ) throws Exception {
 
		FrameInfo addressInfo = globalSymTab.getAddressInfo( mIdentifier );
			
		return addressInfo;
	}
	public ArrayList< CodeBlock > returnIR() throws Exception {
		FrameInfo addressInfo = getAddressInfo();
		if( 0 < mRetVal.size() ) return mRetVal;
		if( !mExpression.isEmpty() )
			mRetVal = addressInfo.generateArraySubscriptCode( mExpression );

		
		return mRetVal;
	}
	
	public ArrayList< CodeBlock > storeIntoLVal( Expression e ) throws Exception{
		if( mLastAssignedExp == e )return mLRetVal;
		mLastAssignedExp = e;
		mLRetVal.clear();
		mLRetVal.addAll( e.returnIR() );
		FrameInfo rval = e.returnOutputTemp();
		FrameInfo addressInfo = getAddressInfo();
		int fixupIndex = mLRetVal.size();
		if( mExpression.isEmpty() )
			mLRetVal.addAll( addressInfo.generateLvalAssignment( rval ) );
		else{
			mLRetVal.addAll( addressInfo.generateLvalAssignment( mExpression,  rval ) );
		}
		e.Fixup( mLRetVal.get( fixupIndex ).label );
		return mLRetVal;
	}
	
	public FrameInfo returnOutputTemp() throws Exception {
		if( mExpression.isEmpty() ){
			FrameInfo fm = this.getAddressInfo();
			return fm;
		}
		if( 0 == mRetVal.size() )
			returnIR();
		
		return mRetVal.get( mRetVal.size() - 1 ).outputTemporary;
	}
	public  Designator( String ident, ArrayList< Expression > expression ){
		super();
		mExpression = expression;
		mIdentifier = ident;
	}
	
	public String opCode(){
		String s = new String();
		s += "Designator---> ";
		s += mIdentifier;
		for( Expression exp : mExpression ){
			s += "[";
			s += exp.opCode();
			s += "]";
		}
		return s;
	}
	public String getMIdentifier() {
		return mIdentifier;
	}
	public void setMIdentifier(String identifier) {
		mIdentifier = identifier;
	}
	public ArrayList< Expression > getMExpression() {
		return mExpression;
	}
	public void setMExpression(ArrayList< Expression > expression) {
		mExpression = expression;
	}
	
	public boolean isArray(){
		if( mExpression.size() > 0 ) return true;
		return false;
	}
}

public static class ExpressionWrapper extends Factor{
	private Expression mExpression;

	public ExpressionWrapper(Expression expression) {
		super();
		mExpression = expression;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception {
		return mExpression.returnIR();
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		return mExpression.returnOutputTemp();
	}
	public String opCode(){
		String s = new String();
		s += "Factor -->  ";
		s += "(";
		s += mExpression.opCode();
		s += ")";
		return s;
	}

	public Expression getMExpression() {
		return mExpression;
	}

	public void setMExpression(Expression expression) {
		mExpression = expression;
	}
}
public static class RelationOperation {
	private Expression mExpLeft, mExpRight;
	private RelationalOperations mRelationalOperator;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	private int condIndex = -1;
	public RelationOperation(Expression expLeft, Expression expRight,
			RelationalOperations relationalOperator) {
		super();
		mExpLeft = expLeft;
		mExpRight = expRight;
		mRelationalOperator = relationalOperator;
	}
	public Expression getMExpLeft() {
		return mExpLeft;
	}
	public void setMExpLeft(Expression expLeft) {
		mExpLeft = expLeft;
	}
	public Expression getMExpRight() {
		return mExpRight;
	}
	public void setMExpRight(Expression expRight) {
		mExpRight = expRight;
	}
	public RelationalOperations getMRelationalOperator() {
		return mRelationalOperator;
	}
	public void setMRelationalOperator(RelationalOperations relationalOperator) {
		mRelationalOperator = relationalOperator;
	}
	public String opCode(){
		String s = new String();
		return s;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( mRetVal.size() > 0 ) return mRetVal;
		
		ArrayList< CodeBlock > expL = mExpLeft.returnIR();
		FrameInfo lval = mExpLeft.returnOutputTemp();
		mRetVal.addAll( expL );
		
		ArrayList< CodeBlock > expR = mExpRight.returnIR();
		FrameInfo rval = mExpRight.returnOutputTemp();
		mRetVal.addAll( expR );
		
		ArrayList< CodeBlock > cmpInverted = CodeBlock.generateInvertedRelOPJump( lval, rval, mRelationalOperator );
		mRetVal.addAll( cmpInverted );
		condIndex = mRetVal.size() - 1;
		return mRetVal;
		
	}
	
	public void fixup( String e ) throws Exception{
		if( -1 == condIndex ) returnIR();
		mRetVal.get( condIndex ).jumpLabel = e;

	}
}
public static class  Number extends Factor {
	public String opCode(){
		String s = new String();
		s += "Number-->";
		s += String.valueOf( mNumber );
		return s;
	}
	public ArrayList< CodeBlock > returnIR() throws Exception {
		if( mRetVal.size() > 0 ) return mRetVal;
		mRetVal.add( CodeBlock.generateMoveNumber(mNumber));
		return mRetVal;
	}
	
	public FrameInfo returnOutputTemp() throws Exception {
		if( mRetVal.size() == 0 )
			returnIR();
		
		return mRetVal.get( mRetVal.size() - 1 ).outputTemporary;
	}
	
	private Integer mNumber;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public Integer getMNumber() {
		return mNumber;
	}
	public void setMNumber(Integer number) {
		mNumber = number;
	}
	public Number(Integer number) {
		super();
		mNumber = number;
	}
}

public static class FunCallWrapper extends Factor {
	public String opCode(){
		String s = new String();
		s += "Function: call Wrapper--->";
		s += mFunCall.opCode();
		return s;
	}
	
	private FunCallStm mFunCall;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public ArrayList< CodeBlock > returnIR() throws Exception {
		//ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
		if( mRetVal.size() > 0 )return mRetVal;
		mRetVal = mFunCall.returnIR();
		return mRetVal;
	}
	
	public void Fixup( String e ) throws Exception{
		mFunCall.Fixup( e );
	}
	public FrameInfo returnOutputTemp() throws Exception {
		return  mFunCall.returnOutputTemp();
	}
	public FunCallStm getMFunCall() {
		return mFunCall;
	}
	public void setMFunCall(FunCallStm funCall) {
		mFunCall = funCall;
	}
	public FunCallWrapper(FunCallStm funCall) {
		super();
		mFunCall = funCall;
	}
	
}
public static abstract class Factor{
	abstract String opCode();
	abstract ArrayList< CodeBlock > returnIR() throws Exception;
	abstract FrameInfo returnOutputTemp() throws Exception;
	public void Fixup( String e ) throws Exception{
	}
}
 
public static class Term{
	private ArrayList< Factor > mFactorList;
	private ArrayList< BinaryOperations > mOperatorList;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public Term(ArrayList<Factor> factorList,
			ArrayList<BinaryOperations> operatorList) {
		super();
		mFactorList = factorList;
		mOperatorList = operatorList;
	}
	
	public void Fixup( String e ) throws Exception{
		if( mFactorList.size() == 0 ) return;
		mFactorList.get( mFactorList.size() - 1 ).Fixup( e );
	}
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( mRetVal.size() > 0 || mFactorList.size() == 0 )return mRetVal;
		ArrayList< CodeBlock > lhsBlock = mFactorList.get( 0 ).returnIR();
		mRetVal.addAll( lhsBlock );
		FrameInfo lhs = mFactorList.get( 0 ).returnOutputTemp();
		int sz = mOperatorList.size();
		for( int i = 0; i < sz; ++i ){
			ArrayList< CodeBlock > rhsBlock = mFactorList.get( i + 1 ).returnIR();
			mRetVal.addAll( rhsBlock );
			FrameInfo rhs = mFactorList.get( i + 1 ).returnOutputTemp();
			int opCode = CodeBlock.TranslateBinOpToOpcode( mOperatorList.get( i ) );
			CodeBlock comb = CodeBlock.generateBinOP( lhs, rhs, opCode );
			lhs = comb.outputTemporary;
			mRetVal.add( comb );
			if( i > 0 && rhsBlock.size() > 0 ){
				mFactorList.get( i - 1 ).Fixup( rhsBlock.get( 0 ).label );
			}
		}
		return mRetVal;
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		if( mFactorList.size() == 1 )
			return mFactorList.get( 0 ).returnOutputTemp();
		if( 0 == mRetVal.size() )
			returnIR();
		if( 0 == mFactorList.size() )
			return null;
		
		return mRetVal.get( mRetVal.size() - 1 ).outputTemporary;
	}
	public ArrayList<Factor> getMFactorList() {
		return mFactorList;
	}
	
	public void setMFactorList(ArrayList<Factor> factorList) {
		mFactorList = factorList;
	}
	public ArrayList<BinaryOperations> getMOperatorList() {
		return mOperatorList;
	}
	public void setMOperatorList(ArrayList<BinaryOperations> operatorList) {
		mOperatorList = operatorList;
	}
	public String opCode(){
		String s = new String();
		int sz = mFactorList.size();
		int opSz = mOperatorList.size();
		for( int i = 0; i < sz; ++ i ){
			Factor curFac = mFactorList.get( i );
			s += curFac.opCode();
			if( i < opSz ){
				s += serializeBinaryOpn( mOperatorList.get( i ) );
			}
		}
		return s;
	}
	
}
public static class Expression{
	private ArrayList< Term > mTermList;
	private ArrayList< BinaryOperations > mOperatorList;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public Expression( ArrayList< Term > termList, ArrayList< BinaryOperations > operatorList ){
		super();
		mTermList = termList;
		mOperatorList = operatorList;
		//returnIR();
	}
	public Boolean isEmpty(){
		return mTermList.size() == 0;
	}
	
	public void Fixup( String e ) throws Exception{
		mTermList.get( mTermList.size() - 1 ).Fixup( e );
	}
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( mRetVal.size() > 0 || mTermList.size() == 0 )return mRetVal;
		ArrayList< CodeBlock > lhsBlock = mTermList.get( 0 ).returnIR();
		mRetVal.addAll( lhsBlock );
		FrameInfo lhs = mTermList.get( 0 ).returnOutputTemp();
		int sz = mOperatorList.size();
		for( int i = 0; i < sz; ++i ){
			ArrayList< CodeBlock > rhsBlock = mTermList.get( i + 1 ).returnIR();
			mRetVal.addAll( rhsBlock );
			FrameInfo rhs = mTermList.get( i + 1 ).returnOutputTemp();
			int opCode = CodeBlock.TranslateBinOpToOpcode( mOperatorList.get( i ) );
			CodeBlock comb = CodeBlock.generateBinOP( lhs, rhs, opCode );
			lhs = comb.outputTemporary;
			mRetVal.add( comb );
			if( i != 0  && rhsBlock.size() > 0 ){
				mTermList.get( i - 1 ).Fixup( rhsBlock.get( 0 ).label );
			}
			lhsBlock = rhsBlock;
		}
		return mRetVal;
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		if( mTermList.size() == 1 )
			return mTermList.get( 0 ).returnOutputTemp();
		if( 0 == mRetVal.size() )
			returnIR();
		if( 0 == mTermList.size() )
			return null;
		
		return mRetVal.get( mRetVal.size() - 1 ).outputTemporary;
	}
	
	public String opCode(){
		String s = new String();
		int sz = mTermList.size();
		int opSz = mOperatorList.size();
		for( int i = 0; i < sz; ++ i ){
			Term curFac = mTermList.get( i );
			s += curFac.opCode();
			if( i < opSz ){
				s += serializeBinaryOpn( mOperatorList.get( i ) );
			}
		}
		return s;
	}
	public ArrayList<Term> getMTermList() {
		return mTermList;
	}
	public void setMTermList(ArrayList<Term> termList) {
		mTermList = termList;
	}
	public ArrayList<BinaryOperations> getMOperatorList() {
		return mOperatorList;
	}
	public void setMOperatorList(ArrayList<BinaryOperations> operatorList) {
		mOperatorList = operatorList;
	}
	
}

public static class IfStm extends stm{
	private RelationOperation mRelOp;
	private ArrayList< stm > mIfList;
	private ArrayList< stm > mElseList;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	private int thenIndex = -1;
	private boolean dontFixupIf = false;
	public String opCode(){
		String s = new String();
		return s;
	}
	public IfStm(RelationOperation relOp, ArrayList<stm> ifList,
			ArrayList<stm> elseList) {
		super();
		mRelOp = relOp;
		mIfList = ifList;
		mElseList = elseList;
	}
	
	public void Fixup( String e ) throws Exception{
		if( thenIndex == -1 ) returnIR();
		if( !this.dontFixupIf  )
			mRetVal.get( thenIndex ).jumpLabel = e;
		if( mElseList.size() <= 0 ){
			mRelOp.fixup( e );
		}
		
		if( this.mIfList.size() > 0 )
			mIfList.get( mIfList.size() - 1 ).Fixup( e );
		if( this.mElseList.size() > 0 )
			mElseList.get( mElseList.size() - 1 ).Fixup( e );
	}
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( mRetVal.size() > 0 ) return mRetVal;
		ArrayList< CodeBlock > relExp = mRelOp.returnIR();
		mRetVal.addAll( relExp );
		
		ArrayList< CodeBlock > thenBlock = new ArrayList< CodeBlock >();
		thenBlock = InterRep.BuildCodeBlock( mIfList );
		mRetVal.addAll( thenBlock );
		CodeBlock jmpUncond = CodeBlock.generateUnCondBranch();
		if( mIfList.size() > 0 && mIfList.get( mIfList.size() - 1  ) instanceof ReturnStm ){
			this.dontFixupIf = true;
		}
		else{
			mRetVal.add( jmpUncond );
			thenIndex = mRetVal.size() - 1;
		}
		ArrayList< CodeBlock > elseBlocks = InterRep.BuildCodeBlock( this.mElseList );
		if( mElseList.size() > 0 ){
			mRetVal.addAll( elseBlocks );
			String tmp = elseBlocks.get( 0 ).label;
			mRelOp.fixup( tmp );
		}
		//to do verify if this fixup changes anything.
		
		return mRetVal;
		
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		return new FrameInfo();
	}
	public RelationOperation getMRelOp() {
		return mRelOp;
	}
	public void setMRelOp(RelationOperation relOp) {
		mRelOp = relOp;
	}
	public ArrayList<stm> getMIfList() {
		return mIfList;
	}
	public void setMIfList(ArrayList<stm> ifList) {
		mIfList = ifList;
	}
	public ArrayList<stm> getMElseList() {
		return mElseList;
	}
	public void setMElseList(ArrayList<stm> elseList) {
		mElseList = elseList;
	}
	
}

public static class WhileStm extends stm{
	public String opCode(){
		String s = new String();
		return s;
	}
	private RelationOperation mRelOp;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	
	private ArrayList< stm > mStatementList;
	public WhileStm(RelationOperation relOp, ArrayList<stm> statementList) {
		super();
		mRelOp = relOp;
		mStatementList = statementList;
	}
	public RelationOperation getMRelOp() {
		return mRelOp;
	}
	public void setMRelOp(RelationOperation relOp) {
		mRelOp = relOp;
	}
	public ArrayList<stm> getMStatementList() {
		return mStatementList;
	}
	public void setMStatementList(ArrayList<stm> statementList) {
		mStatementList = statementList;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( this.mRetVal .size() > 0 ) return mRetVal;
		
		ArrayList< CodeBlock > relBlock = new ArrayList< CodeBlock >();
		relBlock = mRelOp.returnIR();
		mRetVal.addAll( relBlock );
		globalSymTab.AddWhileStm( relBlock.get( 0 ).label );
		ArrayList< CodeBlock > doBlock = new ArrayList< CodeBlock >();
		doBlock = InterRep.BuildCodeBlock( mStatementList );
		mRetVal.addAll( doBlock );
		if( mStatementList.isEmpty() == false )
			this.mStatementList.get( mStatementList.size() - 1 ).Fixup( relBlock.get( 0 ).label );
		CodeBlock unCondJmp = CodeBlock.generateUnCondBranch();
		unCondJmp.jumpLabel = relBlock.get( 0 ).label;
		mRetVal.add( unCondJmp );
		return mRetVal;
		
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		return new FrameInfo();
	}
	
	public void Fixup( String e ) throws Exception{
		mRelOp.fixup( e );
		
	}
}

public static class ReturnStm extends stm{
	public String opCode(){
		String s = new String();
		return s;
	}
	private Expression mExpression;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( mRetVal.size() > 0 ) return mRetVal;
		mRetVal.addAll( mExpression.returnIR() );
		
		CodeBlock moveToRetInfo = CodeBlock.generateMoveOrStoreOP( mExpression.returnOutputTemp(), globalSymTab.getReturnValue( globalSymTab.getCurrentContext() ), CodeBlock.kMOVE );
		mRetVal.add( moveToRetInfo );
		
		CodeBlock unCondBr = CodeBlock.generateUnCondBranch();
		unCondBr.jumpLabel = globalSymTab.getReturnAddressLabel( globalSymTab.getCurrentContext() );
		unCondBr.isReturn = true;
		mRetVal.add( unCondBr );
		return mRetVal;
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		return new FrameInfo();
	}
	public ReturnStm(Expression expression) {
		super();
		mExpression = expression;
	}
	public Expression getMExpression() {
		return mExpression;
	}
	public void setMExpression(Expression expression) {
		mExpression = expression;
	}
}


public static class FunCallStm extends stm{
	private static int mCallNum = 1;
	private int mLocalNum = 0;
	private String mIdentifier;
	private ArrayList< Expression > mExpressionList;
	public String opCode(){
		String s = new String();
		s += mIdentifier;
		for( int i = 0; i < mExpressionList.size(); ++ i )
			s += mExpressionList.get( i ).opCode();
		return s;
	}
	public FunCallStm(String identifier, ArrayList<Expression> expressionList) {
		super();
		mLocalNum = mCallNum++;
		mIdentifier = identifier;
		mExpressionList = expressionList;
	}
	public String getMIdentifier() {
		return mIdentifier;
	}
	public void setMIdentifier(String identifier) {
		mIdentifier = identifier;
	}
	public ArrayList<Expression> getMExpressionList() {
		return mExpressionList;
	}
	public void setMExpressionList(ArrayList<Expression> expressionList) {
		mExpressionList = expressionList;
	}
	
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	/**
	 * Process the arguments from right to left instead of from left to right #HPA project changes.
	 */
	public ArrayList< CodeBlock > returnIR() throws Exception {
		//ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
		if( mRetVal.size() > 0 )return mRetVal;
		ArrayList< Expression > paramList = this.getMExpressionList();
		final List<FrameInfo> formalParams = new ArrayList<FrameInfo>();
		if( !paramList.isEmpty() ){
			for( int i = paramList.size() - 1; i >= 0; --i ){
				FrameInfo y = paramList.get( i ).returnOutputTemp();
				ArrayList< CodeBlock > expCode = paramList.get( i ).returnIR();
				mRetVal.addAll( expCode );
				formalParams.add(y);
			}
			Collections.reverse(formalParams);
		}
		CodeBlock unCond = CodeBlock.generateUnCondBranch();
		unCond.jumpLabel = mIdentifier;
		unCond.isCall = true;
		unCond.fnIndex = this.mLocalNum;
		unCond.operands.addAll(formalParams);
		FrameInfo opTemp = globalSymTab.generateNewFrameInfo( unCond.label );
		unCond.outputTemporary = opTemp;
		mRetVal.add( unCond );
		return mRetVal;
	}
	public void Fixup( String e ) throws Exception{
		String fnName = this.mIdentifier;
		globalSymTab.setReturnInfo( e, fnName );
		
	}
	public FrameInfo returnOutputTemp() throws Exception {
		//FrameInfo fm =  
		//return globalSymTab.getReturnValue( this.getMIdentifier() );
		/*fm.tempID = new String( fm.tempID + String.valueOf( this.mLocalNum ) );
		return fm;*/
		if( null == mRetVal || mRetVal.isEmpty() ){
			returnIR();
		}
		
		return mRetVal.get( mRetVal.size() - 1 ).outputTemporary;
	}
	
}
public static class FrameInfo{
	public Integer framePtr = 0;
	//public String objectIdentifier = new String();
	public String symbolicRegisterName = null;
	public String frameName = new String();
	public Integer frameOffset = 0;
	static final Integer frameWordSize = 4;
	public String tempID = new String();
	public String ssaName = null;
	public Integer frameObjectSize = 4; //default 1 word only
	public String registerPosition = null;
	public ArrayList< Integer > dimensions = null;
	public ArrayList< Integer > dimCache = null;
	private ArrayList< InterRep.CodeBlock > generateIndexCode( ArrayList< Expression > e ) throws Exception {
		ArrayList< InterRep.CodeBlock > retVal = new ArrayList< InterRep.CodeBlock >();
		if( null == dimCache )populateDimCache();
		if( dimCache.size() != e.size() ){
			throw new Exception("Invalid Array Index Specified");
		}
		int sz = dimCache.size();
		CodeBlock lastOp = null;
		for( int i = 0; i < sz; ++i ){
			retVal.addAll( e.get( i ).returnIR() );
			CodeBlock movConst = CodeBlock.generateMoveNumber( dimCache.get( i ) );
			retVal.add( movConst );
			FrameInfo opTemp = movConst.outputTemporary;
			CodeBlock mulCur = CodeBlock.generateBinOP( e.get( i ).returnOutputTemp(), opTemp, CodeBlock.kMUL );
			retVal.add( mulCur );
			if( null == lastOp ){
				lastOp = mulCur;
				continue;
			}
			opTemp = lastOp.outputTemporary;
			CodeBlock addOp = CodeBlock.generateBinOP( opTemp, mulCur.outputTemporary, CodeBlock.kADD );
			retVal.add( addOp );
			lastOp = addOp;
		}
		return retVal;
	}
	private void populateDimCache(){
		if( null == dimensions ) return;
		if( null != dimCache ) return;
		dimCache = new ArrayList< Integer >( );
		for( int i = 0; i < dimensions.size(); ++i ){
			dimCache.add( 1 );
		}
		Integer running = 1;
		for( int i = dimensions.size() - 2; i >= 0; --i ){
			running = running * dimensions.get( i + 1 );
			dimCache.set( i, running );
		}
	}
	public String returnLValueTemporary() throws Exception{
		throw new Exception("cannot return LValue temporary for an array ");
	}
	
	public FrameInfo Clone(){
		FrameInfo cloned = new FrameInfo();
		cloned.frameName = this.frameName;
		cloned.frameObjectSize = this.frameObjectSize;
		cloned.frameOffset = this.frameOffset;
		cloned.framePtr = this.framePtr;
		cloned.tempID = new String( this.tempID );
		if( null != this.ssaName )
			cloned.ssaName = new String( this.ssaName );
		if (null != this.symbolicRegisterName) {
			cloned.symbolicRegisterName = new String (this.symbolicRegisterName);
		} else {
			cloned.symbolicRegisterName = null;
		}
		if (this.registerPosition != null) {
			cloned.registerPosition = new String (this.registerPosition);
		} else {
			cloned.registerPosition = null;
		}
		
		return cloned;
	}
	public String getRegisterPosition() {
		return registerPosition;
	}

	public void setRegisterPosition(String registerPosition) {
		this.registerPosition = registerPosition;
	}
	public String serializeMe() {
		return frameName;
		//return frameName+":"+String.valueOf( frameOffset );
	}
	public String serializeRA() {
		return frameName;
		//return frameName+":"+String.valueOf( frameOffset );
	}
	public ArrayList< CodeBlock > generateLvalAssignment( ArrayList< Expression > e, FrameInfo rval ) throws Exception {
		ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
		CodeBlock movConst = CodeBlock.generateMoveNumber( frameWordSize );
		FrameInfo opTemp = movConst.outputTemporary;
		
		retVal.add( movConst );
		ArrayList< CodeBlock > indexCode = this.generateIndexCode( e );
		retVal.addAll( indexCode );
		CodeBlock mulBinOP = CodeBlock.generateBinOP( indexCode.get( indexCode.size() - 1 ).outputTemporary, opTemp, CodeBlock.kMUL );
		opTemp = mulBinOP.outputTemporary;
		
		retVal.add( mulBinOP );
		CodeBlock addaBinOP = CodeBlock.generateBinOP( this, opTemp, CodeBlock.kADDA );
		opTemp = addaBinOP.outputTemporary;
		
		retVal.add( addaBinOP );
		CodeBlock storeBinOP = CodeBlock.generateMoveOrStoreOP( rval, opTemp, CodeBlock.kSTORE );
		retVal.add( storeBinOP );
		
		return retVal;
	}
	
	public ArrayList< CodeBlock > generateLvalAssignment(  FrameInfo rval ) throws Exception {
		throw new Exception("Invalid LValue Assignment");
	}
	public ArrayList< CodeBlock > generateArraySubscriptCode( ArrayList< Expression > e ) throws Exception {
		ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
		CodeBlock movConst = CodeBlock.generateMoveNumber( frameWordSize );
		FrameInfo opTemp = movConst.outputTemporary;
		
		retVal.add( movConst );
		ArrayList< CodeBlock > indexCode = this.generateIndexCode( e );
		retVal.addAll( indexCode );
		CodeBlock mulBinOP = CodeBlock.generateBinOP( indexCode.get( indexCode.size() - 1 ).outputTemporary, opTemp, CodeBlock.kMUL );
		opTemp = mulBinOP.outputTemporary;
		
		retVal.add( mulBinOP );
		CodeBlock addaBinOP = CodeBlock.generateBinOP( this, opTemp, CodeBlock.kADDA );
		opTemp = addaBinOP.outputTemporary;
		
		retVal.add( addaBinOP );
		CodeBlock loadUnOP = CodeBlock.generateUnOP( opTemp, CodeBlock.kLOAD );
		retVal.add( loadUnOP );
		
		return retVal;
		
		
	}
	
	public String returnRValueTemporary(){
		//used in adda instruction for array address
		//if( ssaName != null ) return ssaName;
		return tempID;
	}
}
public static class LocationInfo extends FrameInfo {
	public Boolean isTemporary = true;
	public FrameInfo Clone(){
		LocationInfo cloned = new LocationInfo();
		cloned.frameName = this.frameName;
		cloned.frameObjectSize = this.frameObjectSize;
		cloned.frameOffset = this.frameOffset;
		cloned.framePtr = this.framePtr;
		cloned.tempID = new String( this.tempID );
		if( null != this.ssaName )
			cloned.ssaName = new String( this.ssaName );
		cloned.isTemporary = this.isTemporary;
		cloned.symbolicRegisterName = this.symbolicRegisterName;
		return cloned;
	}
	public String returnLValueTemporary(){
		//if( ssaName != null ) return ssaName;
		return tempID;
	}
	public ArrayList< CodeBlock > generateArraySubscriptCode( Expression e ){
		return null;
	}

	public ArrayList< CodeBlock > generateLvalAssignment(  FrameInfo rval ) throws Exception {
		//putting this in a new function, is our way of designing when we have to take into account spilling.
		ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock > ();
		CodeBlock cd = CodeBlock.generateMoveOrStoreOP( rval, this, CodeBlock.kMOVE );
		//cd.isLetMoveStatement = true;
		retVal.add(  cd );
		
		return retVal;
	}
	
	public String serializeMe(){
		if(registerPosition!=null) return registerPosition;
		if (symbolicRegisterName != null) {
			return symbolicRegisterName;
		}
		return ((ssaName == null) ? tempID : ssaName);
	}
	
	public String serializeRA(){
		if( ssaName != null ) return ssaName;
		return tempID;
	}
}

public static class ConstFrameInfo extends FrameInfo{
	public Integer constVal = 0;
	public String returnLValueTemporary() throws Exception{
		throw new Exception("cannot return LValue temporary for an constant ");
	}
	
	public FrameInfo Clone(){
		ConstFrameInfo cloned = new ConstFrameInfo();
		cloned.frameName = this.frameName;
		cloned.frameObjectSize = this.frameObjectSize;
		cloned.frameOffset = this.frameOffset;
		cloned.framePtr = this.framePtr;
		cloned.tempID = new String( this.tempID );
		if( null != this.ssaName )
			cloned.ssaName = new String( this.ssaName );
		cloned.constVal = this.constVal;
		cloned.symbolicRegisterName = this.symbolicRegisterName;
		return cloned;
	}
	public String returnRValueTemporary(){
		return String.valueOf( constVal );
	}
	
	public String serializeMe(){
		return String.valueOf( constVal );
	}
	public String serializeRA(){
		return String.valueOf( constVal );
	}
}
public static class VarDecl{
	public ArrayList< String > mIdentList = new ArrayList< String >();
	public Hashtable< String, ArrayList< Integer > > mArrayList = new Hashtable< String, ArrayList< Integer > > ();
	public Hashtable< String, FrameInfo > mAddressInfo = new Hashtable< String, FrameInfo >();
	public ArrayList< FrameInfo > mFormalParamsInfo = new ArrayList< FrameInfo >();
	public ArrayList< String > mFormalsIdent = new ArrayList< String >();
	public FrameInfo mReturnInfo = new FrameInfo();
	public String mReturnAddress = new String();
	public VarDecl(ArrayList<String> identList, Hashtable< String, ArrayList< Integer > > arrayList) {
		mIdentList = identList;
		mArrayList = arrayList;
		mAddressInfo = new Hashtable< String, FrameInfo >();
		mFormalParamsInfo = new ArrayList< FrameInfo >();
		mFormalsIdent = new ArrayList< String >();
		mReturnInfo = new FrameInfo();
		createAddressInfoList();
	}
	
	public void ReplaceKey( String key1, String key2 ){
		
		if( mAddressInfo.containsKey( key1 ) ){
			FrameInfo val = mAddressInfo.remove( key1 );
			val.ssaName = key2;
			mAddressInfo.put( key2, val );
		}
		if( mReturnInfo.tempID == key1 ){
			mReturnInfo.ssaName = key2;
		}
	}
	public void AddFormals( ArrayList< String > formals ){
		int sz = formals.size();
		for( int i = 0; i < sz; ++i ){
			String st = formals.get( i );
			FrameInfo fm = globalSymTab.generateNewFrameInfo( st );
			mFormalsIdent.add( st );
			mFormalParamsInfo.add( fm );
			mIdentList.add( st );
			mAddressInfo.put( st, fm );
		}
	}
	
	public FrameInfo returnFormalInfo( String formal ) throws Exception {
		if(!mFormalsIdent.contains( formal ) )
			throw new Exception("Formal Object not found");
		
		FrameInfo fm = mAddressInfo.get( formal );
		return fm;
	}
	private FrameInfo CreateVarInst( String identifier ){
		LocationInfo locInfo = new LocationInfo();
		locInfo.isTemporary = true;
		locInfo.framePtr = 0;
		locInfo.frameOffset = 0;
		locInfo.tempID =  identifier;
		locInfo.frameName = globalSymTab.getCurrentContext();
		return locInfo;
		
	}
	
	private FrameInfo CreateArrayInst( String identifier, ArrayList< Integer > size ){
		FrameInfo fm = new FrameInfo();
		fm.tempID =  identifier;
		fm.framePtr = 0; //at register allocation we might want to set this to something that points to valid storage.
		fm.frameObjectSize = FrameInfo.frameWordSize;
		fm.dimensions = size;
		for( int dim : fm.dimensions ){
			fm.frameObjectSize *= dim;
		}
		fm.frameOffset = 0; //this is should be  valid frame offset for any reference object.
		fm.frameName = fm.tempID;
		return fm;
	}
	private void createAddressInfoList(){
		int identSize = mIdentList.size();
		for( int i = 0; i < identSize; ++i ){
			String obj = mIdentList.get( i );
			mAddressInfo.put( obj, CreateVarInst( obj ) );
		}
		
		for( Enumeration< String > e = mArrayList.keys(); e.hasMoreElements(); ){
			String key = e.nextElement();
			ArrayList< Integer > size = mArrayList.get( key );
			mAddressInfo.put( key, CreateArrayInst( key, size ) );
		}
	}
	public VarDecl(){
		super();
	}
	public String opCode(){
		String s = new String();
		s += mIdentList.toString();
		s += "Arrays\n";
		s += mArrayList.toString();
		return s;
	}
	public ArrayList<String> getMIdentList() {
		return mIdentList;
	}
	public Hashtable< String, ArrayList< Integer > > getMArrayDimension() {
		return mArrayList;
	}
}
public static class FormalParam{
	private ArrayList< String > mIdent;

	public FormalParam(ArrayList<String> ident) {
		super();
		mIdent = ident;
	}

	public ArrayList<String> getMIdent() {
		return mIdent;
	}

	public void setMIdent(ArrayList<String> ident) {
		mIdent = ident;
	}
	
	public String opCode(){
		String s = new String();
		return s;
	}
}
public static class FunBody{
	private VarDecl mVarDecl;
	private ArrayList< stm > mStmList;
	public FunBody(VarDecl varDecl, ArrayList<stm> stmList) {
		super();
		mVarDecl = varDecl;
		mStmList = stmList;
	}
	public VarDecl getMVarDecl() {
		return mVarDecl;
	}
	public ArrayList<stm> getMStmList() {
		return mStmList;
	}
	public void setMVarDecl(VarDecl varDecl) {
		mVarDecl = varDecl;
	}
	public void setMStmList(ArrayList<stm> stmList) {
		mStmList = stmList;
	}
	public String opCode(){
		String s = new String();
		return s;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception {
		ArrayList< CodeBlock > retVal = new ArrayList< CodeBlock >();
		retVal = InterRep.BuildCodeBlock( mStmList );
		return retVal;
		//globalSymTab.AddContextVars( , vdc)
	}
}

public static class FunDecl{
	private Boolean mFunc;
	private String mIdent;
	private FormalParam mFormalParams;
	private FunBody mFunBody;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public String opCode(){
		String s = new String();
		return s;
	}
	public FunDecl(Boolean func, String ident, FormalParam formalParams,
			FunBody funBody) throws Exception {
		super();
		mFunc = func;
		globalSymTab.SetFnOrProc( ident, func );
		mIdent = ident;
		mFormalParams = formalParams;
		mFunBody = funBody;
		returnIR();
		gCodeTree.AddCodeBlock( mIdent, mRetVal );	
		
	}
	public Boolean getMFunc() {
		return mFunc;
	}
	public String getMIdent() {
		return mIdent;
	}
	public FormalParam getMFormalParams() {
		return mFormalParams;
	}
	public FunBody getMFunBody() {
		return mFunBody;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception {
		if( mRetVal.size() > 0 ) return mRetVal;
		String curContext = globalSymTab.getCurrentContext();
		globalSymTab.AddContextVars( mIdent, mFunBody.getMVarDecl() );
		globalSymTab.SetCurrentContext( mIdent );
		mRetVal.addAll( mFunBody.returnIR() );
		globalSymTab.SetCurrentContext( curContext );
		return mRetVal;
	}
}

public static class Computation{
	private VarDecl mVarDecl;
	private Hashtable< String, FunDecl > mFunDeclList;
	private ArrayList< stm > mStmList;
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public String opCode(){
		String s = new String();
		return s;
	}
	public Computation(VarDecl varDecl, Hashtable<String, FunDecl> funDeclList,
			ArrayList<stm> stmList) {
		super();
		mVarDecl = varDecl;
		mFunDeclList = funDeclList;
		mStmList = stmList;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception{
		if( 0 < mRetVal.size() ) return mRetVal;
		
		globalSymTab.SetCurrentContext( "main" );
		/*for( Enumeration< String > e = mFunDeclList.keys(); e.hasMoreElements();  ) {
			String val = e.nextElement();
			FunDecl fdc = mFunDeclList.get( val );
			mRetVal.addAll( fdc.returnIR() );
		}
		*/
		mRetVal.addAll( InterRep.BuildCodeBlock( mStmList ) );
		gCodeTree.AddCodeBlock( "main", mRetVal );
		//codegen.Process();
		return mRetVal;
		
	}
	public VarDecl getMVarDecl() {
		return mVarDecl;
	}
	public Hashtable<String, FunDecl> getMFunDeclList() {
		return mFunDeclList;
	}
	public ArrayList<stm> getMStmList() {
		return mStmList;
	}
}
public static class AssignmentStm extends stm{
	private Designator mDesig_instance;
	private  Expression  mExpression;
	public String opCode(){
		String s = new String();
		return s;
	}
	private ArrayList< CodeBlock > mRetVal = new ArrayList< CodeBlock >();
	public AssignmentStm( Designator desig_instance, Expression  expression ){
		super();
		mDesig_instance = desig_instance;
		mExpression = expression;
	}
	
	public ArrayList< CodeBlock > returnIR() throws Exception{
		
		if( mRetVal.size() > 0 ) return mRetVal;
		String curContext = globalSymTab.getCurrentContext();
		globalSymTab.SetOptimizeScope( curContext );
		mRetVal = mDesig_instance.storeIntoLVal( mExpression );
		boolean isGlobal = globalSymTab.isGlobal( mDesig_instance.getMIdentifier() );
		if( !mDesig_instance.isArray() && globalSymTab.IsSafeForOptimize( mRetVal.get( mRetVal.size() - 1 ) ) ) mRetVal.get( mRetVal.size() - 1 ).isLetMoveStatement = true;	
		else if( isGlobal )  mRetVal.get( mRetVal.size() - 1 ).isGlobalAssignment = true;
		globalSymTab.ResetOptimizeScope();
		return mRetVal;
	}
	
	public FrameInfo returnOutputTemp() throws Exception{
		if( 0 == mRetVal.size() ) returnIR();
		
		return mRetVal.get( mRetVal.size() - 1 ).outputTemporary;
	}
	public Designator getMDesig_instance() {
		return mDesig_instance;
	}
	public void setMDesig_instance(Designator desig_instance) {
		mDesig_instance = desig_instance;
	}
	public Expression getMExpression() {
		return mExpression;
	}
	public void setMExpression_list( Expression expression) {
		mExpression = expression;
	}
}
}

package CodeGen;
import java.io.*;
import java.util.*;
import intermediateObjects.InterRep;
import cfg.cfg;
import optimizer.OPT;
import DLX.DLX;
public class codegen {
	
	public static final int REGCOUNT = 32;
	private static final int ARCHREGCOUNT = 8;
	public static final int WORDSIZE = 4;
	public static final int DLXSTARTINDEX = 9;
	public static final int DLXTEMPS = 2;//REGCOUNT - 5 - 8;
	public static final int SP = 29;
	public static final int FP = 28;
	public static final int GP = 30;
	public static final int RET = 31;
	public static final int ZERO = 0;
	public static class FuncGenInfo{
		private String mFuncName = new String();
		private HashMap< cfg.CFGBlock, HashSet< Integer > > mKillSets = new HashMap< cfg.CFGBlock, HashSet< Integer > >();
		private HashSet< Integer > mUsedMainRegisters = new HashSet< Integer >();
		private cfg.OPTParamBlock mCodeBlocks = null;
		private HashSet< String > mDirtyGlobals = new HashSet< String >();
		private HashMap< String, ArrayList< String > > mJumpLabels = new HashMap< String, ArrayList< String > >();
		private BlockInfo mBlock = null;
		private cfg.TopologicalSort mTopSort = null;
		public cfg.TopologicalSort returnTopSort(){
			return mTopSort;
		}
		public FuncGenInfo( String name, cfg.TopologicalSort topSort, BlockInfo block, HashMap< cfg.CFGBlock, HashSet< Integer > > killSets, HashSet< Integer > usedMainRegisters, cfg.OPTParamBlock optBlock, HashSet< String > dirtyGlobals, HashMap< String, ArrayList< String > > jumpLabels ){
			super();
			mFuncName = name;
			mTopSort = topSort;
			mBlock = block;
			mKillSets = killSets;
			mUsedMainRegisters = usedMainRegisters;
			mCodeBlocks = optBlock;
			mDirtyGlobals = dirtyGlobals;
			mJumpLabels = jumpLabels;
		}
		public BlockInfo getMBlock(){
			return mBlock;
		}
		public void setMBlock( BlockInfo block ){
			mBlock = block;
		}
		
		public String getMFuncName() {
			return mFuncName;
		}
		public void setMFuncName(String funcName) {
			mFuncName = funcName;
		}
		public HashMap<cfg.CFGBlock, HashSet<Integer>> getMKillSets() {
			return mKillSets;
		}
		public void setMKillSets(HashMap<cfg.CFGBlock, HashSet<Integer>> killSets) {
			mKillSets = killSets;
		}
		public HashSet<Integer> getMUsedMainRegisters() {
			return mUsedMainRegisters;
		}
		public void setMUsedMainRegisters(HashSet<Integer> usedMainRegisters) {
			mUsedMainRegisters = usedMainRegisters;
		}
		public cfg.OPTParamBlock getMCodeBlocks() {
			return mCodeBlocks;
		}
		public void setMCodeBlocks(cfg.OPTParamBlock codeBlocks) {
			mCodeBlocks = codeBlocks;
		}
		public HashSet<String> getMDirtyGlobals() {
			return mDirtyGlobals;
		}
		public void setMDirtyGlobals(HashSet<String> dirtyGlobals) {
			mDirtyGlobals = dirtyGlobals;
		}
		public HashMap<String, ArrayList<String>> getMJumpLabels() {
			return mJumpLabels;
		}
		public void setMJumpLabels(HashMap<String, ArrayList<String>> jumpLabels) {
			mJumpLabels = jumpLabels;
		}
		
	}
	/*public static class VarInfo{
		public int regIndex = -1;
		//Misnomer actually, this is the 
		public int spillIndex = -1;
		public int globalOffsetIndex = -1;
		String varName = new String();
		public VarInfo(){
			super();
		}
		
		public boolean IsValidReg(){
			return regIndex != -1;
		}
		
		public boolean IsValidSpillSlot(){
			return spillIndex != -1;
		}
		
		public boolean IsValidGlobal(){
			return globalOffsetIndex != -1;
		}
		
		private static VarInfo CreateRegBased( int tReg, String name ){
			assert tReg < REGCOUNT;
			VarInfo retVal = new VarInfo();
			retVal.varName = new String( name );
			retVal.regIndex = tReg; 
			return retVal;
		}
		
		private static VarInfo CreateSpillBased( int tSpill, String name, int size ){
			//spillIndex is basically bogus
			VarInfo retVal = new VarInfo();
			retVal.varName = new String( name );
			retVal.spillIndex = codegen.curInfo.AddToNewSpillSlot( name, size );
			return retVal;
		}
		private static VarInfo CreateGlobalBased( int tGlobalOffset, String name, int size ){
			//tglobalOffset is not honored by me
			VarInfo retVal = new VarInfo();
			retVal.varName = new String( name );
			retVal.globalOffsetIndex = codegen.GlobalOffsetTableIndex( name, size );
			return retVal;
		}
		public static VarInfo CreateIDBased( InterRep.FrameInfo fm ){
			String loc = fm.serializeMe();
			if( loc.contains( "$RETURN") ) return null;
			char in = loc.charAt( 0 );
			Integer num = Integer.valueOf( loc.substring( 1 ) );
			switch( in ){
			case 'R':
				return CreateRegBased( num, fm.tempID );
			case 'S':
				return CreateSpillBased( num, fm.tempID, fm.frameObjectSize );
			case 'G':
				return CreateGlobalBased( num, fm.tempID, fm.frameObjectSize );
			}
			
			return null; //coz arrays and main variables already have been assigned a slot and null is handled by the code
		}
		
		public static VarInfo CreateForDecl( InterRep.FrameInfo fm ){
			VarInfo retVal = new VarInfo();
			retVal.varName = fm.tempID;
			retVal.spillIndex = codegen.curInfo.AddToNewSpillSlot( fm.tempID, fm.frameObjectSize );
			return retVal;
		}
	}*/
	public static ArrayList< String > mCurFormals = null;
	public static boolean writeDirtyGlobals = true;
	private static void HandleSpilledArg( int regIndex, String name, String passedLabel ){
		if( regIndex < codegen.DLXSTARTINDEX )return;
		if( codegen.mCurFormals.contains( name ) ){
			codegen.mCurFormals.remove( name );
			codegen.mTempMgr.Dirty( regIndex );
		}
	}
	private static HashMap< String, InterRep.FrameInfo > mArgsMap = null;
	//private static ArrayList< String > sFnInProgress = new ArrayList< Str>
	private static boolean isFnFirstArg( String a, String fn ){
		InterRep.VarDecl vd = InterRep.globalSymTab.getVarDeclInfo( fn );
		ArrayList< String > fmls = vd.mFormalsIdent;
		if( null == fmls || fmls.size() == 0 ){
			return false;
		}
		return fmls.get( 0 ).equals( a );
	}
	private static ArrayList< HashMap< String, InterRep.FrameInfo > > mNestedArgList = new ArrayList< HashMap< String, InterRep.FrameInfo > >();
	private static boolean clearTempsForCall = false;
	//before u judge me for writing such a function it was written 1 day before the demo
	private static boolean IsRegSpillIns( InterRep.CodeBlock refIns ){
		InterRep.FrameInfo srcParam = refIns.operands.get( 0 );
		InterRep.FrameInfo dstParam = refIns.outputTemporary;
		String tempIDSrc = srcParam.tempID;
		String tempIDDest = dstParam.tempID;
		if( tempIDSrc.equals( tempIDDest ) == false ){
			return false;
		}
		String rgSrc = srcParam.registerPosition;
		String rgDst = dstParam.registerPosition;
		if( null == rgSrc || null == rgDst || rgSrc.isEmpty() || rgDst.isEmpty() ){
			return false;
		}
		return rgSrc.charAt( 0 ) == 'R' && rgDst.charAt( 0 ) == 'S';
	}
	public static void HandleMoveInstruction( String passedLabel, InterRep.CodeBlock refIns ){
		InterRep.FrameInfo srcParam = refIns.operands.get( 0 );
		InterRep.FrameInfo dstParam = refIns.outputTemporary;
		int srcReg = 0;
		//int srcReg = mArg.ReturnRegister( srcParam, passedLabel, false );
		//case 1 return tmt
		if( IsRegSpillIns( refIns ) ){
			//spill and free the register
			codegen.mArg.SpillAndFreeReg(refIns, passedLabel);
			return;
		}
		if( refIns.IsReturnOp() ){
			int olSz = codegen.mCurGen.SizeOfIns();
			int regIndex = codegen.mTempMgr.ReturnFromFun( codegen.mCurFn, passedLabel, false );
			int newSz = codegen.mCurGen.SizeOfIns();
			writeDirtyGlobals = false;
			boolean  imm = false;
			if( !( srcParam instanceof InterRep.ConstFrameInfo  ) ){
				srcReg = mArg.ReturnRegister( srcParam, passedLabel, false );
			}else{
				imm = true;
				srcReg = Integer.valueOf( srcParam.tempID );
			}
			
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, srcReg, regIndex, imm );
			int newSz2 = codegen.mCurGen.SizeOfIns();
			if( olSz < newSz ){
				codegen.mCurGen.SetNewEpilog( olSz + 1 ); 
			}
			else if( newSz < newSz2 ){
				codegen.mCurGen.SetNewEpilog( newSz + 1 );
			}
			return;
		}
		//handle arg passing case.
		if( refIns.isArgPassingStatement ){
			if( codegen.isFnFirstArg( refIns.outputTemporary.tempID, refIns.outputTemporary.frameName ) ){
				if( null != mArgsMap ){
					codegen.mNestedArgList.add( mArgsMap );
					mArgsMap = null;
				}
			}
			if( null == mArgsMap ){
				/*if( srcParam.tempID.contains("$RETURN" ) ){
					int indx = srcParam.tempID.lastIndexOf( "$RETURN" );
					String funName = srcParam.tempID.substring( 0, indx );
				}*/
				/*codegen.clearTempsForCall = true;
				mArgsMap = codegen.mTempMgr.CallFun( refIns.outputTemporary.frameName, passedLabel );*/
				mArgsMap = new HashMap< String, InterRep.FrameInfo >();
			}
			mArgsMap.put( refIns.outputTemporary.tempID, srcParam );
		/*	int regIndex = mArgsMap.get( refIns.outputTemporary.tempID );
			//codegen.mTempMgr.Dirty( regIndex );
			if( !(srcParam instanceof InterRep.ConstFrameInfo )  ){
				srcReg = mArg.ReturnRegister( srcParam, passedLabel, false );
				codegen.HandleSpilledArg( srcReg, srcParam.tempID, passedLabel );
			}
			/*else if( srcParam.tempID.contains("$RETURN") ){
				int indx = srcParam.tempID.lastIndexOf( "$RETURN" );
				String funName = srcParam.tempID.substring( 0, indx );
				//int regIndex = 0;
				if( codegen.mTempMgr.IsTempPresent( srcParam.tempID ) ){
					srcReg = mTempMgr.ReturnTemp( srcParam.tempID, passedLabel, false, false );
				}
				else{
					srcReg = mTempMgr.ReturnFromFun( funName, passedLabel );
				}
				//codegen.mTempMgr.ReturnFromFun( , label)
			}
			else{
			//	srcReg = codegen.mTempMgr.ReturnTemp( srcParam.tempID, passedLabel, false, false );
				Integer value = Integer.valueOf( srcParam.tempID );
				codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, value, regIndex, true );
				return;
			}
			
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, srcReg, regIndex, false );*/
			return;
		}
		//case handle argument which is spilled. 
	//	srcReg = mArg.ReturnRegister( srcParam, passedLabel, false );
		/*String srcName = srcParam.tempID;
		if( codegen.mCurFormals.contains( srcName ) ){
			codegen.mTempMgr.Dirty( srcReg );
		}*/
	//	codegen.HandleSpilledArg( srcReg, srcParam.tempID, passedLabel);
		int destReg = mArg.ReturnRegister( dstParam, passedLabel, true );
		if( !(srcParam instanceof InterRep.ConstFrameInfo )  ){
			srcReg = mArg.ReturnRegister( srcParam, passedLabel, false );
			codegen.HandleSpilledArg( srcReg, srcParam.tempID, passedLabel );
		}
		/*else if( srcParam.tempID.contains("$RETURN") ){
			int indx = srcParam.tempID.lastIndexOf( "$RETURN" );
			String funName = srcParam.tempID.substring( 0, indx );
			//int regIndex = 0;
			if( codegen.mTempMgr.IsTempPresent( srcParam.tempID ) ){
				srcReg = mTempMgr.ReturnTemp( srcParam.tempID, passedLabel, false, false );
			}
			else{
				srcReg = mTempMgr.ReturnFromFun( funName, passedLabel );
			}
			//codegen.mTempMgr.ReturnFromFun( , label)
		}*/
		else{
		//	srcReg = codegen.mTempMgr.ReturnTemp( srcParam.tempID, passedLabel, false, false );
			Integer value = Integer.valueOf( srcParam.tempID );
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, value, destReg, true );
			return;
		}
		
		
		//the above does all the dirty mappings and allocates a temp.
		
		//now consider the minor case where in src is a temporary and destination is an arch register, we need to free up that temporary.
		if( srcReg >= codegen.DLXSTARTINDEX && destReg < codegen.DLXSTARTINDEX ){
			codegen.mTempMgr.MoveToReg( destReg, dstParam.tempID, passedLabel );
		}
		else{
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, srcReg, codegen.ZERO, destReg, false );
		}
	}
	
	public static void HandleArithmeticInstruction( String passedLabel, InterRep.CodeBlock refIns ){
		InterRep.FrameInfo srcParam1 = refIns.operands.get( 0 );
		int srcReg1 = -1;
		boolean isImmediate = false;
		//handle the adda case.
		if( refIns.opCode == InterRep.CodeBlock.kADDA ){
			boolean isGlobal = false;
			int pos = codegen.curInfo.SlotPosition( srcParam1.tempID );
			if( -1 == pos ){
				isGlobal = true;
				pos = codegen.mainBlockInfo.SlotPosition( srcParam1.tempID );
			}
			String tempVarName = srcParam1.tempID + "$PASSREF";
			boolean isTempPresent = codegen.mTempMgr.IsTempPresent( tempVarName );
			srcReg1 = codegen.mTempMgr.ReturnTemp( tempVarName, passedLabel, false, false );
			int tmpReg = 0;
			if( isGlobal ){
				tmpReg = codegen.GP;
			}
			else{
				tmpReg = codegen.FP;
			}
			//if( !)
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, tmpReg, pos, srcReg1, true );
		}
		else if( !( srcParam1 instanceof InterRep.ConstFrameInfo ) ){
			srcReg1 = codegen.mArg.ReturnRegister( srcParam1, passedLabel, false );
			codegen.HandleSpilledArg( srcReg1, srcParam1.tempID, passedLabel );
		}
		else{
			isImmediate = true;
		}
		InterRep.FrameInfo srcParam2 = refIns.operands.get( 1 );
		int srcReg2 = -1;
		if( !( srcParam2 instanceof InterRep.ConstFrameInfo ) ){
			srcReg2 = codegen.mArg.ReturnRegister( srcParam2, passedLabel, false );
			codegen.HandleSpilledArg( srcReg2, srcParam2.tempID, passedLabel);
		}
		else if( isImmediate ){
			srcReg2 = codegen.mTempMgr.ReturnTemp( srcParam2.tempID, passedLabel, false, false );
			Integer value = Integer.valueOf( srcParam2.tempID );
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, value, srcReg2, true );
		}
		else{
			isImmediate = true;
		}
		int destRegIndex = mArg.ReturnRegister( refIns.outputTemporary, passedLabel, true );
		if( isImmediate ){
			int validReg = -1;
			int value = 0;
			if( -1 != srcReg1 ){
				validReg = srcReg1;
				value = Integer.valueOf( srcParam2.tempID );
			}
			else{
				if( InterRep.CodeBlock.kSUB == refIns.opCode || InterRep.CodeBlock.kCMP == refIns.opCode ){
					srcReg1 = codegen.mTempMgr.ReturnTemp( srcParam1.tempID, passedLabel, false, false );
					codegen.mCurGen.CreateArithmeticIns( passedLabel, refIns.opCode, srcReg1, srcReg2, destRegIndex, false );
					return;
				}
				validReg = srcReg2;
				value = Integer.valueOf( srcParam1.tempID );
			}
			codegen.mCurGen.CreateArithmeticIns( passedLabel, refIns.opCode, validReg, value, destRegIndex, true );
		}
		else{
			codegen.mCurGen.CreateArithmeticIns( passedLabel, refIns.opCode, srcReg1, srcReg2, destRegIndex, false );
		}
	}
	private static void HandleFnArgs( String passedLabel, InterRep.CodeBlock refIns ){
		String funName = refIns.jumpLabel;
		InterRep.VarDecl varDecls = InterRep.globalSymTab.getVarDeclInfo( funName );
		ArrayList< String > args = varDecls.mFormalsIdent;
		if( null == mArgsMap || args == null || args.size() == 0 ) return;
		for( String arg : args ){
			InterRep.FrameInfo fm = mArgsMap.get( arg );
			int regIndex = 0;
			if( fm instanceof InterRep.ConstFrameInfo ){
				regIndex = codegen.mTempMgr.ReturnTemp( fm.tempID, passedLabel, false, false );
				Integer value = Integer.valueOf( fm.tempID );
				codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, value, regIndex, true );
			}
			else{
				regIndex = codegen.mArg.ReturnRegister( fm, passedLabel, false );
			}
			codegen.mCurGen.StackOperations( passedLabel, regIndex, codegen.SP, codegen.WORDSIZE, true );
			codegen.curInfo.IncrRunningBlock( codegen.WORDSIZE );
		}
		
	}
	
	private static int ReturnRegForGlobalFun( String passedLabel, InterRep.CodeBlock refIns ){
		String funName = refIns.jumpLabel;
		InterRep.VarDecl varDecls = InterRep.globalSymTab.getVarDeclInfo( funName );
		ArrayList< String > args = varDecls.mFormalsIdent;
		if( null == mArgsMap && args.size() < 1 ) return 0;
		String arg = args.get( 0 );
		InterRep.FrameInfo fm = mArgsMap.get( arg );
		int regIndex = 0;
		if( fm instanceof InterRep.ConstFrameInfo ){
			regIndex = codegen.mTempMgr.ReturnTemp( fm.tempID, passedLabel, false, false );
			Integer value = Integer.valueOf( fm.tempID );
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, value, regIndex, true );
		}
		else{
			regIndex = codegen.mArg.ReturnRegister( fm, passedLabel, false );
		}
		
		return regIndex;
	}
	public static void HandleJmpInstructions( String passedLabel, InterRep.CodeBlock refIns ){
		int passedReg = 0;
		if( refIns.isCall ){
			//codegen.mArgsMap = null;
			//String retName = refIns.jumpLabel + "$RETURN";
			//codegen.curInfo.RemoveSpillSlot( retName, -1 );
			if( !codegen.clearTempsForCall ){
				codegen.mTempMgr.CallFun( refIns.jumpLabel, passedLabel );
				if( InterRep.globalSymTab.isGlobalFun( refIns.jumpLabel ) ){
					if( refIns.jumpLabel.equals("InputNum") ){
						passedReg = codegen.mTempMgr.ReturnTemp( "__param_for_global", passedLabel, false, false );
					}
					else if( refIns.jumpLabel.equals( "OutputNum" ) ){
						passedReg = ReturnRegForGlobalFun( passedLabel, refIns );
					}
					
				}
				else{
					HandleFnArgs( passedLabel, refIns );
				}
				
				
			}
			else{
				codegen.clearTempsForCall = false;
			}
			if( codegen.mNestedArgList.size() > 0 ){
				codegen.mArgsMap = codegen.mNestedArgList.remove( codegen.mNestedArgList.size() - 1 );
			}
			else{
				codegen.mArgsMap = null;
			}
		}
		else if( refIns.isReturn ){
			codegen.mCurGen.CreateEpilog( passedLabel, codegen.writeDirtyGlobals );
			return;
		}
		else{
			if( refIns.opCode != InterRep.CodeBlock.kBRA ){
				InterRep.FrameInfo param = refIns.operands.get( 0 );
				passedReg = codegen.mArg.ReturnRegister( param, passedLabel, false );
			}
		}
		codegen.mCurGen.CreateJumpIns( passedLabel, refIns, passedReg );
		if( refIns.isCall && InterRep.globalSymTab.IsFnOrProc( refIns.jumpLabel ) ){
			//int retIndex = codegen.DLXSTARTINDEX;
			//int offset = codegen.curInfo.
			//SEXY stuff
			String retName = refIns.outputTemporary.tempID;
			int destReg = mArg.ReturnRegister( refIns.outputTemporary, passedLabel, true );
			//String retName = refIns.jumpLabel + "$RETURN" + String.valueOf( refIns.fnIndex );
			int regPos = codegen.mTempMgr.ReturnFromFun( refIns.jumpLabel, passedLabel, true );
			codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, regPos, codegen.ZERO, destReg, true );
		//	mTempMgr.Remap( retName1, retName );
			//int slotPos = codegen.curInfo.AddToSpillSlotWhileRunning( passedLabel, retName, -1 );
			//codegen.mCurGen.LSInstructions( passedLabel, regPos, codegen.FP, slotPos, false, false );
		//	codegen.mTempMgr.Dirty( codegen.DLXSTARTINDEX );
		//	codegen.mTempMgr.FreeTemp( passedLabel, codegen.DLXSTARTINDEX );
		}
	}
	public static void HandleLoadStoreInstructions( String passedLabel, InterRep.CodeBlock refIns ){
		
		int srcReg = 0;
		int reg2 = 0;
		boolean isLoad = refIns.opCode == InterRep.CodeBlock.kLOAD;
		int opNum = 0;
		if( !isLoad ){
			opNum = 1;
		}
		InterRep.FrameInfo srcParam = refIns.operands.get( opNum );
		srcReg = codegen.mArg.ReturnRegister( srcParam, passedLabel, false );
		if( !isLoad ){
			InterRep.FrameInfo srcParam2 = refIns.operands.get( 0 );
			if( !( srcParam2 instanceof InterRep.ConstFrameInfo ) ){
				reg2 = codegen.mArg.ReturnRegister( refIns.operands.get( 0 ), passedLabel, false );
				codegen.HandleSpilledArg( reg2, srcParam2.tempID, passedLabel );
			}
			else{
				reg2 = codegen.mTempMgr.ReturnTemp( srcParam2.tempID, passedLabel, false, false );
				Integer value = Integer.valueOf( srcParam2.tempID );
				codegen.mCurGen.CreateArithmeticIns( passedLabel, InterRep.CodeBlock.kADD, codegen.ZERO, value, reg2, true );
			}
		}
		else{
			InterRep.FrameInfo dstParam = refIns.outputTemporary;
			reg2 = codegen.mArg.ReturnRegister( dstParam, passedLabel, true );
		}
		codegen.mCurGen.LSInstructions( passedLabel, reg2, srcReg, 0, isLoad, false );
	}
	public static class BlockInfo{
		private String tagFuncLabel = new String();
		private int blockSize = 0;
		private int lastAddedBlock = 0;
		private int runningBlockSize = WORDSIZE;
		//public HashMap< String, VarInfo > varsMap = new HashMap< String, VarInfo >();
		private HashMap< String, Integer > spilledMap = new HashMap< String, Integer >();
		public BlockInfo(){
			super();
		}
		
		public void IncrRunningBlock( Integer size ){
			runningBlockSize += size; 
		}
		public void Remap( String from, String to ){
			if( this.spilledMap.containsKey( from ) ){
				int val = this.spilledMap.remove( from );
				this.spilledMap.put( to, val );
			}
		}
		public void AddBackOffset( String s, int backOffset ){
			//\m/..\m/
			if( this.spilledMap.containsKey( s ) )return;
			spilledMap.put( s , backOffset );
		}
		public int ReturnBlockSize(){
			return blockSize;
		}
		/*public void AddToVarsMap( VarInfo var ){
			if( null == var || varsMap.containsKey( var.varName ) ) {
				return;
			}
			varsMap.put( var.varName, var );
		}*/
		public void FunctionStarts(){
			//heads up.
			blockSize += lastAddedBlock;
			lastAddedBlock = 0;
			this.runningBlockSize = blockSize;
			codegen.mTempMgr.CallFun( codegen.mCurGen.mFunName, null );
			//always change sp by blockSize and use runningBlocksize for dynamic spills.
			codegen.mCurGen.CreateProlog( blockSize );
			
		}
		public int AddToNewSpillSlot( String tempID, int size ){
			if( !spilledMap.containsKey( tempID ) ){
				/*if( 0 == blockSize ){
					blockSize = WORDSIZE;
				}*/
				blockSize += ( this.lastAddedBlock + codegen.WORDSIZE );
				spilledMap.put( tempID, blockSize );
				/*int oldBlk = blockSize;
				assert size % WORDSIZE == 0;*/
				lastAddedBlock = size - WORDSIZE;
				return blockSize;
			}
			return spilledMap.get( tempID );
		}
		
		public boolean LoadFromSpillSlot( String varname, int regIndex, String label ){
			if( !spilledMap.containsKey( varname ) ){
				return false;
			}
			int c = spilledMap.get( varname );
			int usereg = codegen.FP;
			if( this == codegen.mainBlockInfo ){
				usereg = codegen.GP;
			}
			codegen.mCurGen.LSInstructions( label, regIndex, usereg, c, true, false );
			return true;
		}
		
		public int SlotPosition( String tempID ){
			int pos = -1;
			if( spilledMap.containsKey( tempID  ) ){
				pos = spilledMap.get( tempID );
			}
			return pos;
		}
		public int AddToSpillSlotWhileRunning( String label, String tempID, int regIndex ){
			//size is implicit
			int oldSize = 0;
			if( !spilledMap.containsKey( tempID ) ){
				/*if( 0 == runningBlockSize ){
					runningBlockSize = WORDSIZE;
				}*/
				runningBlockSize += ( lastAddedBlock + codegen.WORDSIZE );
			//	codegen.mCurGen.CreateArithmeticIns(label, InterRep.CodeBlock.kADD, srcRegIndex1, srcRegIndex2, destRegIndex, isImmediate)
				if( -1 != regIndex ){
					codegen.mCurGen.StackOperations(label, regIndex, codegen.SP, codegen.WORDSIZE, true );
				}
				else{
					codegen.mCurGen.CreateArithmeticIns( label, InterRep.CodeBlock.kADD, codegen.SP, codegen.WORDSIZE, codegen.SP, true );
				}
				
				spilledMap.put( tempID, runningBlockSize );
				/*oldSize = runningBlockSize;
				runningBlockSize += WORDSIZE;*/
				lastAddedBlock = 0;
				return runningBlockSize;
			}
			else{
				oldSize = spilledMap.get( tempID );
			}
			int usereg = codegen.FP;
			if( this == codegen.mainBlockInfo ){
				usereg = codegen.GP;
			}
			if( -1 != regIndex ){
				codegen.mCurGen.LSInstructions(label, regIndex, usereg, oldSize, false, false );
			}
			
			return oldSize;
			//return 
		}
		public int RemoveSpillSlot( String tempID, int regHint ){
			if( spilledMap.containsKey( tempID ) ){
				spilledMap.remove( tempID );
			}
			return 0;
		}
	}
	
	public static HashMap< String, BlockInfo > blockData = new HashMap< String, BlockInfo >();
	//public static HashMap< String, ArrayList< String > > jumpLabels = new HashMap< String, ArrayList< String > >();
	public static HashMap< String, String > callDefn = new HashMap< String, String >()	;
	public static HashMap< String, codegen.FuncGenInfo > functionParams = new HashMap< String, codegen.FuncGenInfo >();
//	public static ArrayList< Integer > globalsOffsetFromBottom = new ArrayList< Integer >();
	
	public static int GlobalOffsetTableIndex( String tempID, int size ){
		if( mainBlockInfo.spilledMap.containsKey( tempID ) ){
			//well too much messy to have R30 point below
			//this is not what the project spec says but this is easier to get working.
			return  mainBlockInfo.spilledMap.get( tempID );
		}
		return -1;
	}
	public static BlockInfo curInfo = null;
	public static BlockInfo mainBlockInfo = null;
	public static codegen.CodeGenerator mCurGen = null;
	//public static HashMap< String, cfg.OPTParamBlock > codeBlocks = new HashMap< String, cfg.OPTParamBlock >();
	public static BlockInfo NewBlock( String funName ){
		BlockInfo newBlock = new BlockInfo();
		blockData.put( funName, newBlock );
		curInfo = newBlock;
		if( funName.equals( "main" ) ){
			mainBlockInfo = newBlock;
		}
		return newBlock;
	}
	
	public static void ResetCurBlock(){
		curInfo = null;
		codegen.mArg = null;
		codegen.mArgsMap = null;
		codegen.mCurFn = null;
		codegen.mCurFormals = null;
		codegen.mTempMgr = null;
	}
	
	private static void BranchLabel( InterRep.CodeBlock cdBlk, HashMap< String, ArrayList< String > > jumpLabels ){
		if( 11 <= cdBlk.opCode && cdBlk.opCode <= 17 && !cdBlk.isDeleted && !cdBlk.isCall && !cdBlk.isReturn ){
			if( jumpLabels.containsKey( cdBlk.jumpLabel ) ){
				jumpLabels.get( cdBlk.jumpLabel ).add( cdBlk.label );
				return;
			}
			ArrayList< String > theNewList = new ArrayList< String >();
			theNewList.add( cdBlk.label );
			jumpLabels.put( cdBlk.jumpLabel, theNewList );
		}
	}
	private static void PreProcessForFunc( String fun  ){
		InterRep.VarDecl theVars = InterRep.globalSymTab.getVarDeclInfo( fun );
		boolean isMain = fun.equals("main");
		Hashtable< String,InterRep.FrameInfo > addInfo = theVars.mAddressInfo;
		Set< String > arrayNames = theVars.mArrayList.keySet();
		for( String s : arrayNames ){
			InterRep.FrameInfo fm = addInfo.get( s );
			codegen.curInfo.AddToNewSpillSlot( fm.tempID, fm.frameObjectSize );
			//VarInfo vi = VarInfo.CreateForDecl( fm );
			//codegen.curInfo.AddToVarsMap( vi );
		}
		if( isMain ){
			for( String s : theVars.mIdentList ){
				InterRep.FrameInfo fm = addInfo.get( s );
				codegen.curInfo.AddToNewSpillSlot( fm.tempID, fm.frameObjectSize );
				//VarInfo vi = VarInfo.CreateForDecl( fm );
				//codegen.curInfo.AddToVarsMap( vi );
			}
		}
	}
	private static int RegisterIndex( InterRep.FrameInfo fm ){
		String regPos = fm.registerPosition;
		Integer regnum = -1;
		if( null != regPos && regPos.startsWith( "R" ) ){
			regnum = Integer.valueOf( regPos.substring( 1 ) );
		}
		return regnum + 1;
	}
	private static boolean DidUseMainRegister( InterRep.CodeBlock cdBlk, HashSet< Integer > usedMainReg ){
		if( cdBlk.isDeleted )
			return false;
		boolean changed = false;
		for( InterRep.FrameInfo fm : cdBlk.operands ){
			int regpos = RegisterIndex( fm );
			if( 0 != regpos && !usedMainReg.contains( regpos ) ){
				usedMainReg.add( regpos );
				changed = true;
			}
			if( cdBlk.opCode == InterRep.CodeBlock.kMOVE ){
				break;
			}
		}
		if( cdBlk.opCode != InterRep.CodeBlock.kSTORE ){
			int regpos = RegisterIndex( cdBlk.outputTemporary );
			if( 0 != regpos && !usedMainReg.contains( regpos ) ){
				usedMainReg.add( regpos );
				changed = true;
			}
		}
		return changed;
	}
	
	private static boolean DidChangeGlobal( InterRep.CodeBlock cdBlk, HashSet< String > dirtyGlobals ){
		if( cdBlk.isDeleted || cdBlk.opCode == InterRep.CodeBlock.kSTORE ){
			return false;
		}
		boolean changed = false;
		String opTemp = cdBlk.outputTemporary.registerPosition;
		if( null != opTemp && opTemp.startsWith("G") && !dirtyGlobals.contains( cdBlk.outputTemporary.tempID ) ){
			dirtyGlobals.add( cdBlk.outputTemporary.tempID );
			changed = true;
		}
		return changed;
	}
	public static void PreProcess( String funName, cfg.OPTParamBlock theParam ){
		//need to call this for each optparamblock
		if( funName.equals("boo") ){
			boolean a = true;
		}
		NewBlock( funName );
		HashMap< String, ArrayList< String > > jumpLabels = new HashMap< String, ArrayList< String > >();
		HashSet< Integer > usedMainRegisters = new HashSet< Integer >();
		HashSet< String > dirtyGlobals = new HashSet< String >();
		//codegen.codeBlocks.put( funName, theParam );
		PreProcessForFunc( funName );
		String firstStmt = null;
		cfg.TopologicalSort topSort = new cfg.TopologicalSort( theParam.root );
		ArrayList< cfg.CFGBlock > toVisit = topSort.ReturnSorted();
		for( cfg.CFGBlock theBlock : theParam.vertex ){
			if( theBlock.isDeleted ){
				continue;
			}
			InterRep.CodeBlock lastNode = null;
			for( InterRep.CodeBlock cdBlk : theBlock.GetStatementsList() ){
				if( cdBlk.isDeleted || cdBlk.isArgPassingStatement ){
					continue;
				}
				lastNode = cdBlk;
				codegen.DidUseMainRegister( cdBlk, usedMainRegisters );
				codegen.DidChangeGlobal( cdBlk, dirtyGlobals );
			/*	if( firstStmt == null ){
					firstStmt = cdBlk.label;
					codegen.callDefn.put( funName, firstStmt );
				}
				for( InterRep.FrameInfo fm : cdBlk.operands ){
					//curInfo.AddToVarsMap( VarInfo.CreateIDBased( fm ) );
					if( cdBlk.opCode == InterRep.CodeBlock.kMOVE )break;
				}
				if( cdBlk.opCode == InterRep.CodeBlock.kSTORE ){
					continue;
				}
			//	curInfo.AddToVarsMap( VarInfo.CreateIDBased( cdBlk.outputTemporary ) ); */
				BranchLabel( cdBlk, jumpLabels );
			}
			//if( null != lastNode ){
				
			//}
		}
		OPT.CodeGenOptimizer codeGen = new OPT.CodeGenOptimizer( funName, theParam );
		codeGen.Optimize( theParam.root );
		HashMap< cfg.CFGBlock, HashSet< Integer > > killedSets = codeGen.ReturnKillSets();
		codegen.FuncGenInfo funGen = new FuncGenInfo( funName, topSort, codegen.curInfo, killedSets, usedMainRegisters, theParam, dirtyGlobals, jumpLabels );
		codegen.functionParams.put( funName, funGen );
		codegen.ResetCurBlock();
	}
	
	public static String mCurFn = null;
	public static HashMap< String, codegen.CodeGenerator > mObjectCode = new HashMap< String, CodeGenerator >();
	public static void Process(){
		Set< String > funSet = codegen.functionParams.keySet();
		for( String s : funSet ){
			codegen.FuncGenInfo fnGen = codegen.functionParams.get( s );
			codegen.mCurGen = new codegen.CodeGenerator( s, fnGen );
			codegen.curInfo = fnGen.getMBlock();
			codegen.mTempMgr = new codegen.TempManager( codegen.DLXTEMPS, codegen.DLXSTARTINDEX, true );
			InterRep.VarDecl varDecls = InterRep.globalSymTab.getVarDeclInfo( s );
			codegen.mCurFormals = varDecls.mFormalsIdent;
			codegen.mCurFn = s;
			codegen.mArg = new codegen.ArgProcessor();
		//	codegen.curInfo.FunctionStarts();
			CompileCurrentFunction( s );
			mObjectCode.put( s, mCurGen );
		//	mCurGen.SerializeDebug();
			codegen.ResetCurBlock();
		}
		Link();
	}
	public static void HandleKillSlots( String passedLabel, String funName, cfg.CFGBlock curBlock ){
		codegen.FuncGenInfo fnGen = codegen.functionParams.get( funName );
		HashSet< Integer > killSlots = fnGen.getMKillSets().get( curBlock );
		if( null == killSlots ) return;
		for( Integer i : killSlots ){
			codegen.mTempMgr.FreeTemp( passedLabel, i );
		}
	}
	private static void Link( ){
		/*codegen.CodeGenerator mainGen = codegen.mObjectCode.get( "main" );
		int mainOff = mainGen.EnqueueFinal();*/
		HashMap< String, ArrayList< Integer > > callSites = new HashMap< String, ArrayList< Integer > >();
		ArrayList< String > fnQueue = new ArrayList< String >();
		fnQueue.add( "main" );
		//Set< String > calls 
		while( fnQueue.isEmpty() == false ){
			String s = fnQueue.remove( 0 );
			codegen.CodeGenerator curGen = codegen.mObjectCode.get( s );
			int fnOff = curGen.EnqueueFinal();
			callSites = curGen.ReturnCallSites();
			Set< String > calls = callSites.keySet();
			for( String fn : calls ){
				boolean rec = false;
				if( fn.equals( s ) ){
					rec = true;
				}
				if( !fnQueue.contains( fn ) && !rec ){
					fnQueue.add( fn );
				}
				ArrayList< Integer > sites = callSites.get( fn );
				CodeGenerator cg = mObjectCode.get( fn );
				int laidDownOff = cg.EnqueueFinal();
				for( Integer i : sites ){
					int off = i + fnOff;
					curGen.FixupCallSite( off, laidDownOff );
				}
			}
		}
		
		CodeGenerator.FixupSP();
		CodeGenerator.DumpStuff();
		//DLX dl = new DLX();
		int[] ret = new int[CodeGenerator.theOneCodeBlock.size()];
	    for (int i=0; i < ret.length; i++)
	    {
	        ret[i] = CodeGenerator.theOneCodeBlock.get(i).intValue();
	    }
		
		DLX.load( ret );
		try{
			DLX.execute();
		}
		catch( Exception e ){
			
		}
	}
	private static cfg.CFGBlock ReturnInorderPred( cfg.CFGBlock node ){
		ArrayList< cfg.CFGBlock > predList = node.PredecessorList();
		for( cfg.CFGBlock pred : predList ){
			if( node.BlockLabel().equals( pred.JumpLabel() ) == false ){
				return pred;
			}
		}
		return null;
	}
	private static ArrayList< cfg.CFGBlock > ReturnInorderParentList( cfg.CFGBlock theNode, HashSet< cfg.CFGBlock > rejectedList ){
		ArrayList< cfg.CFGBlock > visitList = new ArrayList< cfg.CFGBlock >();
		cfg.CFGBlock parent = ReturnInorderPred( theNode );
		while( null != parent && !rejectedList.contains( parent ) ){
			if( visitList.isEmpty() ){
				visitList.add( parent );
			}
			else{
				visitList.add( 0, parent );
			}
			parent = ReturnInorderPred( parent );
		}
		visitList.add( theNode );
		return visitList;
		
	}
	private static void CompileCurrentFunction( String funName ){
		//generate prolog.
		codegen.curInfo.FunctionStarts();
		//HashMap< cfg.CFGBlock, Boolean > visitedMap = new HashMap< cfg.CFGBlock, Boolean >();
		//HashSet< cfg.CFGBlock > visitedSet = new HashSet< cfg.CFGBlock >();
		// now process each instruction in each node. 
		String lastLabel = null;
		if( funName.equals( "main"  ) ){
			boolean a = true;
		}
	//	boolean firstTime = false;
		codegen.FuncGenInfo fnGen = codegen.functionParams.get( funName );
		cfg.OPTParamBlock opt = fnGen.getMCodeBlocks();
		cfg.TopologicalSort topSort = fnGen.returnTopSort();
		ArrayList< cfg.CFGBlock > toVisit = topSort.ReturnSorted();
			for( cfg.CFGBlock blk : toVisit ){
				if( blk.isDeleted ) continue;
				boolean encounteredBr = false;
				String blockLbl = blk.BlockLabel();
				//firstTime = false;
				for( InterRep.CodeBlock cdBlk : blk.GetStatementsList() ){
					if( cdBlk.isDeleted ){
						continue;
					}
				/*	if( null == blockLbl ){
						blockLbl = cdBlk.label;
					}*/
					switch( cdBlk.opCode ){
					case InterRep.CodeBlock.kADD:
					case InterRep.CodeBlock.kSUB:
					case InterRep.CodeBlock.kMUL:
					case InterRep.CodeBlock.kDIV:
					case InterRep.CodeBlock.kADDA:
					case InterRep.CodeBlock.kCMP:
						codegen.HandleArithmeticInstruction( blockLbl, cdBlk );
						break;
					case InterRep.CodeBlock.kLOAD:
					case InterRep.CodeBlock.kSTORE:
						codegen.HandleLoadStoreInstructions( blockLbl, cdBlk );
						break;
					case InterRep.CodeBlock.kMOVE:
						codegen.HandleMoveInstruction( blockLbl, cdBlk );
						break;
					case InterRep.CodeBlock.kBEQ:
					case InterRep.CodeBlock.kBGE:
					case InterRep.CodeBlock.kBGT:
					case InterRep.CodeBlock.kBLE:
					case InterRep.CodeBlock.kBLT:
					case InterRep.CodeBlock.kBNE:
					case InterRep.CodeBlock.kBRA:
						if( !cdBlk.isCall  && !cdBlk.isReturn ){
							encounteredBr = true;
							codegen.HandleKillSlots( blockLbl, funName, blk );
						}
						String lbl = null;
						if( encounteredBr ){
							lbl = cdBlk.label;
						}
						else{
							lbl = blockLbl;
						}
						codegen.HandleJmpInstructions( lbl, cdBlk );
						default:
							boolean a = true;
					}
					
					//blockLbl = null;
				}
				lastLabel = blockLbl;
			/*	if( !visitedSet.contains( blk ) ){
					visitedSet.add( blk );
				}*/
			}			
		if( mCurGen.EpilogDone() == false ){
			mCurGen.CreateEpilog(lastLabel, codegen.writeDirtyGlobals );
		}
		codegen.mCurGen.FixupBranchCalls();
	}
	public static class CodeGenerator{
		private ArrayList< Integer > mFuncInstructions = new ArrayList< Integer >();
		private ArrayList< String > mDebugInstructions = new ArrayList< String >();
		private String mFunName = new String();
		private codegen.FuncGenInfo mGenInfo = null;
		private HashMap< Integer, Integer > mArithmeticMap = new HashMap< Integer, Integer >();
		private HashMap< Integer, String > mArithmeticDebugMap = new HashMap< Integer, String >();
		public void SerializeDebug(){
			System.out.println(mFunName + ":");
			for( int i = 0; i < this.mFuncInstructions.size(); ++i ){
				String s = this.mDebugInstructions.get( i );
				int j = this.mFuncInstructions.get( i );
				System.out.print(  + i + " ## " + s + " : ");
				System.out.println( j );
			}
			//System.out.println
		}
		private static final int kADD = 0;
		private static final int kSUB = 1;
		private static final int kMUL = 2;
		private static final int kDIV = 3;
		private static final int kMOD = 4;
		private static final int kCMP = 5;
		private static final int kOR = 6;
		private static final int kAND = 7;
		private static final int kBIC = 8;
		private static final int kXOR = 9;
		private static final int kLSH = 10;
		private static final int kASH = 11;
		private static final int kCHK = 12;
		private static final int kIOffset = 16;
		private static final int kLDW = 32;
		private static final int kLDX = 33;
		private static final int kPOP = 34;
		private static final int kSTW = 36;
		private static final int kSTX = 37;
		private static final int kPSH = 38;
		private static final int kBEQ = 40;
		private static final int kBNE = 41;
		private static final int kBLT = 42;
		private static final int kBGE = 43;
		private static final int kBLE = 44;
		private static final int kBGT = 45;
		private static final int kBSR = 46;
		private static final int kJSR = 48;
		private static final int kRET = 49;
		private static final int kRDD = 50;
		private static final int kWRD = 51;
		private static final int kWRH = 52;
		private static final int kWRL = 53;
		private HashMap< Integer, Integer > mJmpMap = new HashMap< Integer, Integer >();
		private HashMap< Integer, String > mJmpDebugMap = new HashMap< Integer, String >();
		private HashMap< String, Integer > mBuiltinMap = new HashMap< String, Integer >();
		private int mPrologIndex = -1;
		private int mEpilogIndex = -1;
		public void SetNewEpilog( int newIndex ){
			mEpilogIndex = newIndex;
		}
		public int SizeOfIns(){
			return this.mFuncInstructions.size() - 1;
		}
		private void InitializeJmpMap(){
			mJmpMap.clear();
			mJmpMap.put( InterRep.CodeBlock.kBEQ, kBEQ );
			mJmpMap.put( InterRep.CodeBlock.kBNE, kBNE );
			mJmpMap.put( InterRep.CodeBlock.kBLT, kBLT );
			mJmpMap.put( InterRep.CodeBlock.kBGE, kBGE );
			mJmpMap.put( InterRep.CodeBlock.kBLE, kBLE );
			mJmpMap.put( InterRep.CodeBlock.kBGT, kBGT );
			mJmpMap.put( InterRep.CodeBlock.kBRA, kBEQ );
			
			mBuiltinMap.clear();
			mBuiltinMap.put( "OutputNewLine", kWRL );
			mBuiltinMap.put( "OutputNum", kWRD );
			mBuiltinMap.put( "InputNum", kRDD );
			
			mJmpDebugMap.clear();
			mJmpDebugMap.put( InterRep.CodeBlock.kBEQ, "BEQ" );
			mJmpDebugMap.put( InterRep.CodeBlock.kBNE, "BNE" );
			mJmpDebugMap.put( InterRep.CodeBlock.kBLT, "BLT" );
			mJmpDebugMap.put( InterRep.CodeBlock.kBGE, "BGE" );
			mJmpDebugMap.put( InterRep.CodeBlock.kBLE, "BLE" );
			mJmpDebugMap.put( InterRep.CodeBlock.kBGT, "BGT" );
			mJmpDebugMap.put( InterRep.CodeBlock.kBRA, "BEQ" );
		}
		private HashMap< String, ArrayList< String > > branchCache = null;
		private HashMap< String, Integer > mResolvedLabels = new HashMap< String, Integer >();
		private HashMap< String, Integer > mResolvedJumpIns = new HashMap< String, Integer >();
		private HashMap< String, ArrayList< Integer > > mCallSites = new HashMap< String, ArrayList< Integer > >();
		public HashMap< String, ArrayList< Integer > > ReturnCallSites(){
			return mCallSites;
		}
		private Integer offset = 0;
		private boolean enqueued = false;
		public int EnqueueFinal(){
			if( enqueued ) return offset;
			enqueued = true;
			offset = theOneCodeBlock.size();
			theOneCodeBlock.addAll( this.mFuncInstructions );
			theOneDebugCodeBlock.addAll( this.mDebugInstructions );
			return offset;
		}
		public int returnOff(){
			return offset;
		}
		public static ArrayList< Integer > theOneCodeBlock = new ArrayList< Integer >();
		public static ArrayList< String > theOneDebugCodeBlock = new ArrayList< String >();
		public static void DumpStuff(){
			try{
				File file = new File( "./dumped_code.txt");
				boolean exist = file.createNewFile();
				FileWriter fstream = new FileWriter("./dumped_code.txt");
				BufferedWriter out = new BufferedWriter(fstream);
				for( int i = 0; i < CodeGenerator.theOneCodeBlock.size(); ++i ){
					int j = theOneCodeBlock.get( i );
					String str = theOneDebugCodeBlock.get( i );
					String s = (  String.valueOf( i ) + " ## " + str + " : ");
					s = s + String.valueOf( j ) + "\n";
					out.write( s );
					
				}
				//out.write(in.readLine());
				out.close();
			}
			catch( Exception e ){
				
			}
			
			//  System.out.println("File created successfully.");
		}
		
		public static void FixupSP(){
			int val = theOneCodeBlock.size();
			val = 4 * ( val +  1 );
			int indx = 0;
			ArrayList< Integer > tempIns = new ArrayList< Integer >();
			ArrayList< String > debugTempIns = new ArrayList< String >();
			int ins = GenerateF1( codegen.SP, codegen.ZERO, 0, kADD + kIOffset );
			tempIns.add( ins );
			String debugStr = GenerateDebug( "ADDI", codegen.SP, codegen.ZERO, 0 );
			debugTempIns.add( debugStr );
			while( val >= 0x7FF ){
				++indx;
				val = val - 0x7FF;
			}
			for( int i = 0; i < indx; ++i ){
				ins = GenerateF1( codegen.SP, codegen.SP, 0x7FF, kADD + kIOffset );
				tempIns.add( ins );
				debugStr = GenerateDebug( "ADDI", codegen.SP, codegen.SP, 0x7FF );
				debugTempIns.add( debugStr );
			}
			if( val > 0 ){
				ins = GenerateF1( codegen.SP, codegen.SP, val, kADD + kIOffset );
				tempIns.add( ins );
				debugStr = GenerateDebug( "ADDI", codegen.SP, codegen.SP, val );
				debugTempIns.add( debugStr );
			}
			
			for( int i = tempIns.size() - 1; i >=0 ;--i ){
				ins = tempIns.get( i );
				debugStr = debugTempIns.get( i );
				theOneCodeBlock.add( 0, ins );
				theOneDebugCodeBlock.add( 0, debugStr );
			}
		}
		public void FixupCallSite( int insIndex, int tgtIndex ){
			//insIndex = offset + insIndex;
			//int insOpCode = theOneCodeBlock.get( insIndex );
			short offset = ( short )( tgtIndex - ( insIndex ) ); //PC -> next addressable word
			Integer ins = theOneCodeBlock.get( insIndex );
			ins = ( ins & ~0xFFFF ) | ( offset & 0xFFFF );
			this.theOneCodeBlock.set( insIndex, ins );
			//debug stuff
			String str = theOneDebugCodeBlock.get( insIndex );
			int indx = str.lastIndexOf( '|' );
			String temp = new String( str.substring( 0, indx ) );
			str = temp + '|' + String.valueOf( offset );
			this.theOneDebugCodeBlock.set( insIndex, str );
		}
	//	public void GenericInstructionProcessing( )
		private void PopulateArithmeticMap(){
			mArithmeticMap.clear();
			mArithmeticMap.put( InterRep.CodeBlock.kNEG, kSUB );
			mArithmeticMap.put( InterRep.CodeBlock.kADD, kADD );
			mArithmeticMap.put( InterRep.CodeBlock.kSUB, kSUB );
			mArithmeticMap.put( InterRep.CodeBlock.kMUL, kMUL );
			mArithmeticMap.put( InterRep.CodeBlock.kDIV, kDIV );
			mArithmeticMap.put( InterRep.CodeBlock.kCMP, kCMP );
			mArithmeticMap.put( InterRep.CodeBlock.kADDA, kADD );
			
			mArithmeticDebugMap.clear();
			mArithmeticDebugMap.put( InterRep.CodeBlock.kNEG, "SUB" );
			//mArithmeticDebugMap.put( InterRep.CodeBlock.kNEG, kSUB );
			mArithmeticDebugMap.put( InterRep.CodeBlock.kADD, "ADD" );
			mArithmeticDebugMap.put( InterRep.CodeBlock.kSUB, "SUB" );
			mArithmeticDebugMap.put( InterRep.CodeBlock.kMUL, "MUL" );
			mArithmeticDebugMap.put( InterRep.CodeBlock.kDIV, "DIV" );
			mArithmeticDebugMap.put( InterRep.CodeBlock.kCMP, "CMP" );
			mArithmeticDebugMap.put( InterRep.CodeBlock.kADDA, "ADD" );
		}
		
		private static int GenerateF2( int a, int b, int c, int opCode ){
			int retVal = 0;
			if( c<0){
				boolean k = true;
			}
			retVal = opCode << 26 | a << 21 | b << 16  | c;
			return retVal;
		}
		
		private static int GenerateF1( int a, int b, int c, int opCode ){
			int retVal = 0;
			if( c < 0 ){
				boolean z = true;
			}
			retVal = opCode << 26 | a << 21 | b << 16 | ( c & 0xFFFF );
			return retVal;
		}
		
		private static String GenerateDebug( String debugIns, int a, int b, int c ){
			String retVal = new String();
			retVal = debugIns + "|" + String.valueOf( a )+ "|" + String.valueOf( b )+ "|" + String.valueOf( c );
			return retVal;
		}
		private ArrayList< Integer > pushedRegisters = null;
		private void CreateRetIns( int regIndex ){
			int insOpCode = this.kRET;
			String debugStr = "RET";
			int a = 0;
			int b = 0;
			int c = regIndex;
			insOpCode = this.GenerateF2(a, b, c, insOpCode );
			this.mFuncInstructions.add( insOpCode );
			debugStr = this.GenerateDebug(debugStr, a, b, c);
			this.mDebugInstructions.add( debugStr );
		}
		private boolean isRetCreated = false;
		public boolean EpilogDone(){
			return isRetCreated;
		}
		public void CreateEpilog( String label, boolean needToFreeGlobals ){
			/*if( isRetCreated ){
				
			}*/
			isRetCreated = true;
			if( needToFreeGlobals ){
				this.mEpilogIndex = this.mFuncInstructions.size(); //what a hack.LOL
				HashSet< String > globals = this.mGenInfo.getMDirtyGlobals();
				for( String gbl : globals ){
					codegen.mTempMgr.FreeTemp( gbl, label );
				}
			}
			if( -1 == this.mEpilogIndex ){
				this.mEpilogIndex = this.mFuncInstructions.size();
			}
			this.CreateArithmeticIns(label, InterRep.CodeBlock.kADD, codegen.ZERO, codegen.FP, codegen.SP, false );
			
			final int negVal = 0-codegen.WORDSIZE;
			this.StackOperations(label, codegen.FP, codegen.SP, negVal, false );
			for( int i = pushedRegisters.size() - 1; i >= 0; --i ){
				int a = pushedRegisters.get( i );
				this.StackOperations(label, a, codegen.SP, negVal, false );
			}
			if( this.mFunName.equals("main") == false ){
				this.StackOperations(label, codegen.RET, codegen.SP, negVal, false );
				//this.CreateJumpIns(label, retIns, codegen.RET );
				this.CreateRetIns( codegen.RET );
				
			}
			else{
				//this.CreateJumpIns(label, retIns, codegen.ZERO );
				this.CreateRetIns( codegen.ZERO );
			}
			//this.EnsureBranchResolved( new String("") );
			
		}
		public void CreateProlog( int spInitialSize ){
			pushedRegisters = new ArrayList< Integer >();
			int offset = 0;
			this.StackOperations( null, codegen.RET, codegen.SP, codegen.WORDSIZE, true );
			offset -= codegen.WORDSIZE;
			this.mPrologIndex = this.mFuncInstructions.size() - 1;
		//	pushedRegisters.add( codegen.RET );
			HashSet< Integer > usedMainRegisters = this.mGenInfo.getMUsedMainRegisters();
			for( Integer reg : usedMainRegisters ){
				this.StackOperations( null, reg,codegen.SP, codegen.WORDSIZE, true );
				pushedRegisters.add( reg );
				offset -= codegen.WORDSIZE;
			}
			this.StackOperations( null, codegen.FP, codegen.SP, codegen.WORDSIZE, true );
			offset -= codegen.WORDSIZE;
			InterRep.VarDecl vr = InterRep.globalSymTab.getVarDeclInfo( mFunName );
			if( null != vr ){
				ArrayList< String > fmls = vr.mFormalsIdent;
				if( null != fmls && fmls.size() > 0 ){
					for( int i = fmls.size() - 1; i >= 0; --i ){
						String fml = fmls.get( i );
						codegen.curInfo.AddBackOffset( fml, offset );
						offset -= codegen.WORDSIZE;
					}
				}
			}
			this.CreateArithmeticIns( null, InterRep.CodeBlock.kADD, codegen.ZERO, codegen.SP, codegen.FP, false );
			if( this.mFunName.equals("main" ) ){
				this.CreateArithmeticIns( null, InterRep.CodeBlock.kADD, codegen.ZERO, codegen.FP, codegen.GP, false );
			}
			if( 0 != spInitialSize ){
				this.CreateArithmeticIns( null, InterRep.CodeBlock.kADD, codegen.SP, spInitialSize, codegen.SP, true );
			}
		}
		public void CreateJumpIns( String label, InterRep.CodeBlock refIns, int regIndex ){
			int insOpCode = mJmpMap.get( refIns.opCode );
			String debugStr = this.mJmpDebugMap.get( refIns.opCode );
			int code = 1;
			int c = 0;
			int a = 0;
			int b = 0;
			boolean isBuiltin = false;
			if( refIns.isCall ){
				insOpCode = this.kBSR;
				debugStr = "BSR";
				if( this.mBuiltinMap.containsKey( refIns.jumpLabel ) ){
					insOpCode = this.mBuiltinMap.get( refIns.jumpLabel );
					debugStr = new String( refIns.jumpLabel );
					isBuiltin = true;
					code = 2;
					if( insOpCode == kRDD ){
						a = regIndex;
						b = 0;
						c = 0;
					}
					else if( kWRD == insOpCode || kWRH == insOpCode ){
						a = 0;
						b = regIndex;
						c = 0;
					}
					else{
						a = 0;
						b = 0;
						c = 0;
						code = 1;
					}
				}
				//code = 3;
			}
			else if( refIns.isReturn ){
				insOpCode = this.kRET;
				debugStr = "RET";
				code = 2;
				c = regIndex;
			}
			else if( refIns.opCode == InterRep.CodeBlock.kBRA ){
				insOpCode = this.kBEQ;
				debugStr = "BEQ";
				a = 0;
				b = 0;
				c = 0;
			}
			else{
				a = regIndex;
			}
			String curLabel = refIns.label;
			
			switch( code ){
			case 1:
				insOpCode = GenerateF1( a, b, c, insOpCode );
				debugStr = this.GenerateDebug( debugStr, a, b, c);
				break;
			case 2:
				insOpCode = GenerateF2( a, b, c, insOpCode );
				debugStr = this.GenerateDebug( debugStr, a, b, c);
			}
			this.mFuncInstructions.add( insOpCode );
			this.mDebugInstructions.add( debugStr );
			this.EnsureBranchResolved( label );
			if( !this.mResolvedJumpIns.containsKey( curLabel ) && !refIns.isCall && !refIns.isReturn ){
				this.mResolvedJumpIns.put( curLabel, mFuncInstructions.size() - 1 );
			}
			if( !isBuiltin && refIns.isCall ){
				if( this.mCallSites.containsKey( refIns.jumpLabel ) ){
					mCallSites.get( refIns.jumpLabel ).add( mFuncInstructions.size() - 1 );
				}
				else{
					ArrayList< Integer > temp = new ArrayList< Integer >();
					temp.add( mFuncInstructions.size() - 1 );
					mCallSites.put( refIns.jumpLabel, temp );
				}
			}
		}
		
		public void CreateArithmeticIns( String label, int opCode, int srcRegIndex1, int srcRegIndex2, int destRegIndex, boolean isImmediate ){
			//String label = refIns.label;
			//this.EnsureBranchResolved( label );
			int insOpCode = mArithmeticMap.get( opCode );
			if( isImmediate ){
				insOpCode += CodeGenerator.kIOffset;
			}
			String debugStr = this.mArithmeticDebugMap.get( opCode );
			if( isImmediate ){
				debugStr = new String( debugStr + "I" );
			}
			//YUCK
			int ins = 0;
			//int ins = insOpCode << 26 | destRegIndex << 21 | srcRegIndex1 << 16 | 0x0000;
			if( isImmediate ){
				//ins = ins | ( srcRegIndex2 & 0xFFFF );
				ins = GenerateF1( destRegIndex, srcRegIndex1, srcRegIndex2, insOpCode );
			}
			else{
			//	ins = ins | srcRegIndex2;
				ins = GenerateF2( destRegIndex, srcRegIndex1, srcRegIndex2, insOpCode );
			}
			this.mFuncInstructions.add( ins );
			this.EnsureBranchResolved( label );
			//debug stuff.
			String retStr = new String();
			//retStr = debugStr + "|" + String.valueOf(destRegIndex ) + "|" + String.valueOf( srcRegIndex1 ) + "|" + String.valueOf( srcRegIndex2 );
			retStr = GenerateDebug( debugStr, destRegIndex, srcRegIndex1, srcRegIndex2 );
			this.mDebugInstructions.add( retStr );
		}
		
		public void LSInstructions( String label, int a, int b, int c, boolean isLoad, boolean isIndexed ){
			int ins = 0;
			//String label = refIns.label;
			String debugStr = new String();
			if( isLoad){
				ins = CodeGenerator.kLDW;
				debugStr = "LDW";
				if( isIndexed ){
					debugStr = "LDX";
				}
			}
			else{
				ins = CodeGenerator.kSTW;
				debugStr = "STW";
				if( isIndexed ){
					debugStr = "STX";
				}
			}
			if( isIndexed ){
				ins++;
				ins = GenerateF2( a, b, c, ins );
			}
			else{
				ins = GenerateF1( a, b, c, ins );
			}
			debugStr = GenerateDebug( debugStr, a, b, c );
			this.mFuncInstructions.add( ins );
			this.EnsureBranchResolved( label );
			
			this.mDebugInstructions.add( debugStr );
		}
		
		public void StackOperations( String label, int a, int b, int c, boolean isPush ){
			String debugStr = new String();
			int ins = 0;
			if( isPush ){
				ins = CodeGenerator.kPSH;
				debugStr = "PSH";
			}
			else{
				ins = CodeGenerator.kPOP;
				debugStr = "POP";
			}
			ins = GenerateF1( a, b, c, ins );
			this.mFuncInstructions.add( ins );
			debugStr = GenerateDebug( debugStr, a, b, c );
			this.mDebugInstructions.add( debugStr );
			this.EnsureBranchResolved( label );
		}
		private void FixupBranchCalls(){
			if( null == branchCache ){
				branchCache = this.mGenInfo.getMJumpLabels();
			}
			Set< String > keys = branchCache.keySet();
			for( String key : keys ){
				ArrayList< String > vals = branchCache.get( key );
				
				int tgtIndex = 0;
				if( key.equals("") ){
					tgtIndex = this.mEpilogIndex;
				}
				else{
					tgtIndex = mResolvedLabels.get( key );
				}
					
				for( String val : vals ){
					if( val.equals( "factIter:12"  ) ){
						boolean a = true;
					}
					int insIndex = mResolvedJumpIns.get( val );
					short offset = ( short )( tgtIndex - ( insIndex ) ); //PC -> next addressable word
					Integer ins = this.mFuncInstructions.get( insIndex );
					ins = ( ins & ~0xFFFF ) | ( offset & 0xFFFF );
					this.mFuncInstructions.set( insIndex, ins );
					
					//debug stuff
					String str = this.mDebugInstructions.get( insIndex );
					int indx = str.lastIndexOf( '|' );
					String temp = new String( str.substring( 0, indx ) );
					str = temp + '|' + String.valueOf( offset );
					this.mDebugInstructions.set( insIndex, str );
				}
			}
		}
	//	private int isBranchResolved( String)
		private void EnsureBranchResolved( String label ){
			if( null == branchCache ){
				branchCache = this.mGenInfo.getMJumpLabels();
			}
			if( branchCache.isEmpty() || null == label || mResolvedLabels.containsKey( label ) ){
				return;
			}
			int curIndex = this.mFuncInstructions.size() - 1;
			if( branchCache.containsKey( label ) ){
				mResolvedLabels.put( label, curIndex );
			}
		}
		public CodeGenerator( String funName, FuncGenInfo genInfo ){
			super();
			mFunName = funName;
			mGenInfo = genInfo;
			PopulateArithmeticMap();
			this.InitializeJmpMap();
		}
		
	}
	/*public static class MemoryManager{
		public MemoryManager(){
			super();
		}
		public HashMap< storageArea, BlockInfo > spilledSlot = new HashMap< storageArea, BlockInfo >();
		public int spillRegister( storageArea area ){
			if( !spilledSlot.containsKey( area ) ){
				spilledSlot.put( area, curInfo );
			}
			return curInfo.AddToNewSpillSlot( area.tempID, WORDSIZE ); //code too spill will go here
		}
		
		public int RestoreSpilledRegister( storageArea area, int regHint ){
			BlockInfo inf = spilledSlot.get( area );
			int regIndex = inf.RemoveSpillSlot( area.tempID, regHint );
			return regIndex;
		}
		
	}
	public static MemoryManager memMgr = new MemoryManager();
	public static abstract class storageArea{
		public String tempID = new String();
		public abstract int returnRegisterIndex();
		public abstract void invalidateRegisterIndex();
		public abstract void restoreRegisterIndex();
		public abstract void dirty();
		public storageArea( String id ){
			super();
			tempID = id;
		}
	}
	
	*/
	public static class TempManager{
		private int mNoOfTemps = 0;
		private int mStartIndex = codegen.DLXSTARTINDEX;
		private boolean mGenerateCode = true;
		private ArrayList< Integer > mFreeList = null;
		private ArrayList< Integer > mFullList = null;
		private int mNextFullPointer = -1;
		private ArrayList< String > mTempIDs = null;
		private HashSet< Integer > dirtyTemps = new HashSet< Integer > ();
		private HashMap< String, Boolean > mGlobalOrSlot = new HashMap< String, Boolean >();
		private void Initialize(){
			mFreeList = new ArrayList< Integer >( mNoOfTemps );
			for( int i = 0; i < mNoOfTemps; ++i ){
				mFreeList.add( mStartIndex + i );
			}
			mFullList = new ArrayList< Integer >();
			mTempIDs = new ArrayList< String >( mNoOfTemps );
			for( int i = 0; i < mNoOfTemps; ++i ){
				mTempIDs.add( null );
			}
			
		}
		
		public boolean MoveToReg( int regIndex, String varname, String label ){
			int indx = this.mTempIDs.indexOf( varname );
			if( -1 == indx ){
				return false;
			}
			indx = indx + mStartIndex;
			codegen.mCurGen.CreateArithmeticIns(label, InterRep.CodeBlock.kADD, codegen.ZERO, indx, regIndex, false );
			this.FreeTemp( label, indx );
			return true;
		}
		public void Dirty( String varname ){
			int indx = mTempIDs.indexOf( varname );
			if( -1 == indx ){
				return;
			}
			indx = indx + this.mStartIndex;
			if( !dirtyTemps.contains( indx ) ){
				dirtyTemps.add( indx );
			}
		}
		public void Dirty( int regIndex ){
			if( !dirtyTemps.contains( regIndex ) ){
				dirtyTemps.add( regIndex );
			}
		}
		public int ReturnTemp( String varname, String label, boolean isOpTemp, boolean isGlobal ){
			int indx = mTempIDs.indexOf( varname );
			if( isOpTemp ){
				Dirty( indx + mStartIndex );
			}
			if( -1 != indx ) return indx + mStartIndex;
			return AllocateNewTemp( varname, label, isOpTemp, isGlobal );
		}
		public boolean IsTempPresent( String varname ){
			return -1 != mTempIDs.indexOf( varname );
		}
		private void UpdateGlobalSet( String tempID, boolean isGlobal ){
			if( !this.mGlobalOrSlot.containsKey( tempID ) ){
				this.mGlobalOrSlot.put( tempID, isGlobal );
			}
			
		}
		
		private void RemoveGlobalSet( String tempID ){
			if( this.mGlobalOrSlot.containsKey( tempID ) ){
				mGlobalOrSlot.remove( tempID );
			}
		}
		
		private boolean ReturnGlobal( String tempID ){
			if( this.mGlobalOrSlot.containsKey( tempID ) ){
				return this.mGlobalOrSlot.get( tempID ); 
			}
			return InterRep.globalSymTab.isGlobal( tempID  );
		}
		private int AllocateNewTemp( String varname, String label, boolean isOpTemp, boolean isGlobal ){
			int retVal = -1;
			boolean needSpill = false;
			this.UpdateGlobalSet( varname, isGlobal );
			if( null == mFreeList || mFreeList.isEmpty() ){
				needSpill = true;
			}
			else{
				retVal = mFreeList.remove( 0 );
				if( mFullList.isEmpty() || mFullList.size() <= retVal - this.mStartIndex ){
					mFullList.add( retVal );
				}
				else{
					mFullList.add( retVal - this.mStartIndex, retVal );
				}
				mTempIDs.set( retVal - mStartIndex, varname );
			}
			if( !mGenerateCode && -1 != retVal ){
				return retVal;
			}
			else if( mGenerateCode && -1 != retVal ){
				//codegen.mCurGen.LSInstructions(label, a, b, c, isLoad, isIndexed)
				if( isOpTemp ){
					this.Dirty( retVal );
				}
				else{
					//will need to load the value
					boolean a = true;
					if( !isGlobal ){
						a = codegen.curInfo.LoadFromSpillSlot(varname, retVal, label );
					}
					else if( isGlobal ){
						a = codegen.mainBlockInfo.LoadFromSpillSlot(varname, retVal, label );
					}
					if( !a ){
						boolean b = true;
					}
				}
			}
			else if( -1 == retVal && !mGenerateCode ){
				mNextFullPointer = ( mNextFullPointer + 1 ) % mNoOfTemps;
				retVal = mFullList.get( mNextFullPointer );
				String dummy = mTempIDs.get( retVal - mStartIndex );
				this.RemoveGlobalSet( dummy );
				mTempIDs.set( retVal - mStartIndex, varname );
				return retVal;
			} 
			else if( -1 == retVal && mGenerateCode ){
				mNextFullPointer = ( mNextFullPointer + 1 ) % mNoOfTemps;
				retVal = mFullList.get( mNextFullPointer );
				if( this.dirtyTemps.contains( retVal ) ){
					this.dirtyTemps.remove( retVal );
					String temp = mTempIDs.get( retVal - mStartIndex );
					codegen.curInfo.AddToSpillSlotWhileRunning(label, temp, retVal );
				}
				//mTempIDs.set( re, element)
				String dummy = mTempIDs.get( retVal - mStartIndex );
				this.RemoveGlobalSet( dummy );
				mTempIDs.set( retVal - mStartIndex, varname );
				if( isOpTemp ){
					this.Dirty( retVal );
				}
			}
			//the whole label business comes to picture when we kind of are gonna generate code, but that is later.
			return retVal;
		}
		//example of myopic bad design and to work around this add another global :D
		public HashMap< String, Integer > CallFun( String funName, String label ){
			HashMap< String, Integer > retVal = new HashMap< String, Integer >();
		/*	InterRep.VarDecl varDecls = InterRep.globalSymTab.getVarDeclInfo( funName );
			ArrayList< String > formals = varDecls.mFormalsIdent;*/
			if( !mGenerateCode ){
				Initialize();
			}
			else{
				this.FreeAllTemps( label );
				//SEXY stuff
				/*InterRep.FrameInfo retInfo = varDecls.mReturnInfo;
				codegen.curInfo.AddToSpillSlotWhileRunning(label, retInfo.tempID, -1 );*/
			}
		/*	if( null == formals || formals.isEmpty() ) return retVal;
			for( String fm : formals ){
				int nextTemp = this.AllocateNewTemp( fm, label, true, false );
				retVal.put( fm, nextTemp );
			}*/
			return retVal;
		}
		
		public int ReturnFromFun( String funName, String label, boolean force ){
			InterRep.VarDecl varDecls = InterRep.globalSymTab.getVarDeclInfo( funName );
			String returnInfo = varDecls.mReturnInfo.tempID;
			if( !mGenerateCode || force ){
				Initialize();
			}
			else{
				this.FreeAllTemps( label );
			}
			return AllocateNewTemp( returnInfo, label, false, false );
		}
	/*	public int ReturnFromFunWithoutCode( String funName ){
			InterRep.VarDecl varDecls = InterRep.globalSymTab.getVarDeclInfo( funName );
			String returnInfo = varDecls.mReturnInfo.tempID;
			Initialize();
			return AllocateNewTemp( )
		}*/
		public void FreeAllTemps( String label ){
			for( int i = 0; i < codegen.DLXTEMPS; ++i ){
				this.FreeTemp(label, mStartIndex + i );
			}
		}
		
	/*	public void AllocateTemp( String varname, String label, int regIndex, boolean isGlobal ){
			FreeTemp( label, regIndex );
			this.UpdateGlobalSet( varname, isGlobal );
			int retVal = this.mFreeList.remove( regIndex - mStartIndex );
			if( retVal != mStartIndex ){
				boolean a = true;
			}
			
			
		}*/
		public void FreeTemp( String varname, String label ){
			int indx = this.mTempIDs.indexOf( varname );
			if( -1 == indx ) return;
			indx = this.mStartIndex + indx;
			FreeTemp( label, indx );
		}
		public void FreeTemp( String label, int regIndex ){
			if( this.mFreeList.contains( regIndex ) ) {
				return;
			}
			if( this.mGenerateCode && this.dirtyTemps.contains( regIndex ) ){
				dirtyTemps.remove( regIndex );
				String dummy = this.mTempIDs.get( regIndex - mStartIndex );
				boolean isGlobal = this.ReturnGlobal( dummy );
				if( isGlobal ){
					codegen.mainBlockInfo.AddToSpillSlotWhileRunning(label, dummy, regIndex );
				}
				else{
					codegen.curInfo.AddToSpillSlotWhileRunning(label, dummy, regIndex );
				}
			}
			this.RemoveGlobalSet( this.mTempIDs.get( regIndex - mStartIndex ) );
			int indx = this.mFullList.indexOf( regIndex );
			this.mFullList.remove( indx );
			//this.mFullList.remove( regIndex - this.mStartIndex );
			if( this.mNextFullPointer >= 0 ){
				mNextFullPointer = mNextFullPointer - 1;
			}
			if( mFreeList.isEmpty() ){
				this.mFreeList.add( regIndex );
			}
			else{
				mFreeList.add( regIndex - this.mStartIndex, regIndex );
			}
			this.mTempIDs.set( regIndex - mStartIndex, null );
		}
		public void Remap( String from, String to ){
			int indx = this.mTempIDs.indexOf( from );
			if( -1 != indx ){
				this.mTempIDs.set( indx , to );
				if( this.mGlobalOrSlot.containsKey( from ) ){
					boolean val = this.mGlobalOrSlot.remove( from );
					this.mGlobalOrSlot.put( to, val );
					/*if( !val ){
						codegen.curInfo.Remap( from, to );
					}
					else{
						codegen.mainBlockInfo.Remap( from, to );
					}*/
				}
			}
		}
		public TempManager( int noOfTemps, int startingIndex, boolean generateCode ){
			super();
			mNoOfTemps = noOfTemps;
			mStartIndex = startingIndex;
			mGenerateCode = generateCode;
			Initialize();
		}
	}
	public static TempManager mTempMgr = null;
	public static class ArgProcessor{
		private ArrayList< String > mArchRegisterSet = new ArrayList< String >();
		private int mNextChoice = -1;
		private HashSet< Integer > mDirtySet = new HashSet< Integer >();
		//private A
		public ArgProcessor(){
			super();
			for( int i = 0; i < codegen.ARCHREGCOUNT; ++i ){
				mArchRegisterSet.add( null );
			}
		}
		public void SpillAndFreeReg( InterRep.CodeBlock refIns, String label ){
			InterRep.FrameInfo srcParam = refIns.operands.get( 0 );
			Integer regIndex = Integer.valueOf( srcParam.registerPosition.substring( 1 ) );
			if( mArchRegisterSet.get( regIndex ) == null || srcParam.tempID.equals( mArchRegisterSet.get( regIndex ) ) == false ){
				return;
			}
			String tmp = mArchRegisterSet.get( regIndex );
			codegen.curInfo.AddToSpillSlotWhileRunning(label, srcParam.tempID, regIndex + 1 );
			mArchRegisterSet.set( regIndex, null );
			mDirtySet.remove( regIndex );
		}
		private void Spill( String label, String varname, int regIndex ){
			if( mArchRegisterSet.get( regIndex ) == null || varname.equals( mArchRegisterSet.get( regIndex ) ) == false ){
				return;
			}
			String tmp = mArchRegisterSet.get( regIndex );
			codegen.curInfo.AddToSpillSlotWhileRunning( label, varname, regIndex + 1 );
			mArchRegisterSet.set( regIndex, null );
			mDirtySet.remove( regIndex );
		}
		public void UseRegister( int regIndex, String varname, String label, boolean isOpTemp ){
			if( mArchRegisterSet.get( regIndex ) != null & varname.equals( this.mArchRegisterSet.get( regIndex ) ) ){
				if( isOpTemp && !this.mDirtySet.contains( regIndex ) ){
					mDirtySet.add( regIndex );
				}
				return;
			}
			else if( mArchRegisterSet.get( regIndex ) != null ){
				boolean a = true; // need to study why this would be true.
				/*if( this.mDirtySet.contains( regIndex ) ){
					Spill( label, varname, regIndex );
				}*/
			}
			if( isOpTemp && !this.mDirtySet.contains( regIndex ) ){
				this.mDirtySet.add( regIndex );
			}
			this.mArchRegisterSet.set( regIndex, varname );
			boolean didMove = codegen.mTempMgr.MoveToReg( regIndex + 1, varname, label );
			if( !didMove ){
				didMove = codegen.curInfo.LoadFromSpillSlot( varname, regIndex + 1, label );
				if( !didMove ){
					didMove = codegen.mainBlockInfo.LoadFromSpillSlot( varname, regIndex + 1, label );
				}
			}	
		}
		private int FirstFree( String label, String tmp, boolean allocateReg ){
			int indx = mArchRegisterSet.indexOf( tmp );
			/*if( -1 != indx ){
				return indx + 1;
			}
			indx = mArchRegisterSet.indexOf( null );
			if( -1 == indx ){
				mNextChoice = ( mNextChoice + 1 ) % codegen.ARCHREGCOUNT;
				indx = mNextChoice;
				//String var = new String( this.mArchRegisterSet.get( mNextChoice ) );
				UseRegister( indx, tmp, label );
				
			}*/
			return indx + 1;
		}
		public int ReturnRegister( InterRep.FrameInfo fm, String label, boolean isOpTemp ){
			String varname = fm.tempID;
			String regPos = fm.registerPosition;
			if( null == regPos ){
				if( varname.contains("$RETURN") ){
					return codegen.mTempMgr.ReturnTemp(varname, label, isOpTemp, false );
				}
				else{
					return codegen.mTempMgr.ReturnTemp(varname, label, isOpTemp, InterRep.globalSymTab.isGlobal( varname ) );
				}
			}
			int usereg = 0;
			if( regPos.charAt( 0 ) == 'R' ){
				usereg = Integer.valueOf( regPos.substring( 1 ) );
				UseRegister( usereg, varname, label, isOpTemp );
				return usereg + 1;
			}
			else if( regPos.charAt( 0 ) == 'S' || regPos.charAt( 0 ) == 'G' ){
				return codegen.mTempMgr.ReturnTemp(varname, label, isOpTemp, regPos.charAt( 0 ) == 'G' ) ;
			}
			return 0;
		}
	}
	public static ArgProcessor mArg = null;
}

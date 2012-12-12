package optimizer;
import cfg.cfg;
import intermediateObjects.InterRep;
import java.util.*;
import CodeGen.codegen;
public class OPT {

	public static abstract class Optimizer{
		protected Queue< cfg.CFGBlock > nodeQueue = new LinkedList< cfg.CFGBlock >();
		abstract void PreProcess( cfg.CFGBlock theRoot );
		abstract void PostProcess( cfg.CFGBlock theRoot );
		abstract void NewTraversal();
		public void Optimize( cfg.CFGBlock theRoot ){
			PreProcess( theRoot );
			nodeQueue.add( theRoot );
			while( nodeQueue.peek() != null ){
				cfg.CFGBlock curNode = nodeQueue.remove();
				NewTraversal();
				Traverse( curNode, null );
			}
			PostProcess( theRoot );
		}
		abstract  void Traverse( cfg.CFGBlock theRoot, cfg.CFGBlock theParent );
		protected boolean Process( cfg.CFGBlock currentVisited, cfg.CFGBlock parent ){
			if( nodeQueue.contains( currentVisited ) ) return true;
			nodeQueue.add( currentVisited );
			return true;
		}
		
		protected void EnsureNotPresent( cfg.CFGBlock theNode ){
			if( nodeQueue.contains( theNode ) ){
				nodeQueue.remove( theNode );
			}
		}
	}
	public static abstract class ForwardOptimizer extends Optimizer{
		 protected void Traverse( cfg.CFGBlock theRoot, cfg.CFGBlock theParent ){
			 if( !Process( theRoot, theParent ) ) return;
			 for( cfg.CFGBlock theSucc : theRoot.SuccessorList() ) {
				 Traverse( theSucc, theRoot );
			 }
		 }
		 
	}
	public static  class CodeGenOptimizer extends ForwardOptimizer{
		private int mNumOfTemps = codegen.DLXTEMPS;
		private int mStartIndex = codegen.DLXSTARTINDEX;
		private HashMap< cfg.CFGBlock, ArrayList< String > > mAvblSet = new HashMap< cfg.CFGBlock, ArrayList< String > >();
		private HashMap< cfg.CFGBlock, ArrayList< cfg.CFGBlock > > mParentsVisited = new HashMap< cfg.CFGBlock, ArrayList< cfg.CFGBlock > >();
		private cfg.OPTParamBlock optParamBlock = null;
		private BitSet theBits = new BitSet();
		private String mFunName = new String();
		private codegen.TempManager mTempMgr = null;
		private Set< String > mHashSet = null;
		private HashMap< cfg.CFGBlock, HashSet< Integer > > mKillSets = new HashMap< cfg.CFGBlock, HashSet< Integer > >();
		public HashMap< cfg.CFGBlock, HashSet< Integer > >  ReturnKillSets(){
			return mKillSets;
		}
		
		public CodeGenOptimizer( String funName, cfg.OPTParamBlock opt ){
			super();
			mFunName = funName;
			optParamBlock = opt;
			theBits = new BitSet( optParamBlock.vertex.size() );
			theBits.clear();
		}
		private void SetVisitedBit( cfg.CFGBlock theNode ){
			Integer index = optParamBlock.dfnum.get( theNode );
			theBits.set( index );
		}
		private boolean isBitSet( cfg.CFGBlock theNode ){
			Integer index = optParamBlock.dfnum.get( theNode );
			return theBits.get( index );
		}
	
		protected void NewTraversal(){
			theBits.clear();
		}
		
		private ArrayList< String > InitializeEmptyTempList(){
			ArrayList< String > retVal = new ArrayList< String >( mNumOfTemps );
			for( int i = 0; i < mNumOfTemps; ++i ){
				retVal.add( null );
			}
			return retVal;
		}
		
		protected void PreProcess( cfg.CFGBlock theRoot ){
			for( cfg.CFGBlock theBlock : this.optParamBlock.vertex ){
				ArrayList< String > initedList = this.InitializeEmptyTempList();
				this.mAvblSet.put( theBlock, initedList );
				this.mParentsVisited.put( theBlock, new ArrayList< cfg.CFGBlock >() );
			}
			this.mTempMgr = new codegen.TempManager( codegen.DLXTEMPS, codegen.DLXSTARTINDEX, false );
			HashMap< String, Integer > argList = mTempMgr.CallFun( this.mFunName, null ); //just for the sake of it.
			mHashSet = argList.keySet();
		//	theBits = new 
		}
		
		protected void PostProcess( cfg.CFGBlock theRoot ){
			if( this.mFunName.equals("boo") ){
				Set< cfg.CFGBlock > keySet = this.mKillSets.keySet();
				for( cfg.CFGBlock key : keySet ){
					HashSet< Integer > val = this.mKillSets.get( key );
					System.out.println("the current node : " + key.BlockLabel() );
					for( Integer ans : val ){
						System.out.print( ans );
						System.out.print("   ");
					}
					System.out.println("End of Set " + key.BlockLabel() );
				}
			}
		}
		private boolean IsSpillSlot( InterRep.FrameInfo fm ){
			if( fm instanceof InterRep.ConstFrameInfo || null == fm.registerPosition ) return false;
			return fm.registerPosition.charAt( 0 ) == 'S' || fm.registerPosition.charAt( 0 ) == 'G';
		}
		
		private void FunctionCalled( ArrayList< String > parentAvblSet, cfg.CFGBlock currentVisited, cfg.CFGBlock parent ){
			ArrayList< cfg.CFGBlock > parentsVisited = this.mParentsVisited.get( currentVisited );
			for( int i = 0; i < parentAvblSet.size(); ++i ){
				String parStr = parentAvblSet.get( i );
				if( null == parStr ){
					continue;
				}
				boolean mismatch = false;
				for( cfg.CFGBlock pt : parentsVisited ){
					ArrayList< String > pTemps = this.mAvblSet.get( pt );
					String sibStr = pTemps.get( i );
					if( !parStr.equals( sibStr ) ){
						//different temid is mapped to that location there is a mismatch.
						mismatch = true;
						break;
					}
				}
				if( !parentsVisited.contains( parent ) ){
					parentsVisited.add( parent );
				}
				if( mismatch ){
					for( cfg.CFGBlock pt : parentsVisited ){
						ArrayList< String > pTemps = this.mAvblSet.get( pt );
						String str = pTemps.get( i );
						if( null == str ) continue;
						EnsureKillSetPresent( pt );
						HashSet< Integer > killSet = this.mKillSets.get( pt );
						if( !killSet.contains( i + this.mStartIndex ) ){
							killSet.add( i + this.mStartIndex ); //this will ensure that when code is being generated at the end of the block the temporary is freed up
						}
					}
				}
			}
		}
		private void EnsureKillSetPresent( cfg.CFGBlock node ){
			if( this.mKillSets.containsKey( node ) )return;
			HashSet< Integer > val = new HashSet< Integer >();
			this.mKillSets.put( node, val );
		}
		private boolean IsArgAndPresentInReg( InterRep.FrameInfo fm ){
			boolean isArg = this.mHashSet.contains( fm.tempID );
			int regnum = 0;
			String registerPosition = fm.registerPosition;
			if( isArg && null != registerPosition && registerPosition.charAt( 0 ) == 'R' ){
				return true;
			}
			return false;
		}
		protected boolean Process( cfg.CFGBlock currentVisited, cfg.CFGBlock parent ){
			if( currentVisited.isDeleted ){
				return false;
			}
			ArrayList< String > parentAvblSet = this.InitializeEmptyTempList();
			if( null != parent ){
				parentAvblSet = ( ArrayList< String > )( this.mAvblSet.get( parent ).clone() );
			}
			ArrayList< String > currentAvblSet = this.mAvblSet.get( currentVisited );
			boolean alreadyVisited = false;
			if( this.isBitSet( currentVisited ) ){
				alreadyVisited = true;
			}
			ArrayList< String > defSet = this.InitializeEmptyTempList();
			this.SetVisitedBit( currentVisited );
			ArrayList< InterRep.CodeBlock > stmts = currentVisited.GetStatementsList();
			for( InterRep.CodeBlock cdBlk : stmts ){
				if( cdBlk.isDeleted ){
					continue;
				}
				if( cdBlk.isCall ){
					this.FunctionCalled(parentAvblSet, currentVisited, parent );
					mTempMgr.ReturnFromFun( this.mFunName, null, false ); //this is a bug here, but all functions behave identically, do not have the tempo to write a string parsing routine now
					parentAvblSet = this.InitializeEmptyTempList();
					defSet = this.InitializeEmptyTempList();
					continue;
				}
				for( InterRep.FrameInfo fm : cdBlk.operands ){
					if( ( IsSpillSlot( fm ) && this.mHashSet.contains( fm.tempID ) ) ){
						mHashSet.remove( fm.tempID );
						int indx = mTempMgr.ReturnTemp( fm.tempID, null, false, false );
						defSet.set( indx - this.mStartIndex, fm.tempID );
					}
					else if(   this.IsArgAndPresentInReg( fm ) ){
						mHashSet.remove( fm.tempID );
						int indx = mTempMgr.ReturnTemp( fm.tempID, null, false, false );
						defSet.set( indx - this.mStartIndex, null );
						mTempMgr.FreeTemp( cdBlk.label, indx );
					}
					if( cdBlk.opCode == InterRep.CodeBlock.kMOVE )break;
				}
				if( cdBlk.opCode != InterRep.CodeBlock.kSTORE ){
					if( IsSpillSlot( cdBlk.outputTemporary ) ){
						int indx = mTempMgr.ReturnTemp( cdBlk.outputTemporary.tempID, null, true, cdBlk.outputTemporary.registerPosition.charAt( 0 ) == 'G' );
						defSet.set( indx - this.mStartIndex, cdBlk.outputTemporary.tempID );
					}
					else if(   this.IsArgAndPresentInReg( cdBlk.outputTemporary ) ){
						mHashSet.remove( cdBlk.outputTemporary.tempID );
						int indx = mTempMgr.ReturnTemp( cdBlk.outputTemporary.tempID, null, true,  cdBlk.outputTemporary.registerPosition.charAt( 0 ) == 'G' );
						defSet.set( indx - this.mStartIndex, null );
						mTempMgr.FreeTemp( cdBlk.label, indx );
					}
				}
			}
			
			boolean changed = false;
			for( int i = 0; i < defSet.size(); ++i ){
				String defVar = defSet.get( i );
				String avblVar = currentAvblSet.get( i );
				String parVar = parentAvblSet.get( i );
				String finalVar = null;
				//boolean shouldSet = true;
				if( defVar != null ){
					finalVar = defVar;
				}
				else if( parVar != null ){
					finalVar = parVar;
				}
				else{
					finalVar = avblVar;
				}
				if( finalVar != null && avblVar == null ){
					changed = true;
				}
				parentAvblSet.set( i, finalVar );
			}
			this.mAvblSet.put( currentVisited, parentAvblSet );
			if( !this.mParentsVisited.get( currentVisited ).contains( parent ) ){
				this.mParentsVisited.get( currentVisited ).add( parent );
			}
			if( changed && alreadyVisited ){
				super.Process(currentVisited, parent );
				return false;
			}
			else if( alreadyVisited ){
				return false;
			}
			return true;
		}
	}
	
	
	public static abstract class BackwardOptimizer extends Optimizer{
		 protected void Traverse( cfg.CFGBlock theRoot, cfg.CFGBlock theParent ){
			 if( !Process( theRoot, theParent ) ) return;
			 for( cfg.CFGBlock thePred : theRoot.PredecessorList() ) {
				 Traverse( thePred, theRoot );
			 }
		 }
	}

	public static class CommonSubexpressionElimination extends ForwardOptimizer{
		private cfg.OPTParamBlock optParamBlock = null;
		private BitSet theBits = new BitSet( );
		private void SetVisitedBit( cfg.CFGBlock theNode ){
			Integer index = optParamBlock.dfnum.get( theNode );
			theBits.set( index );
		}
		private boolean somethingChanged = false;
		public boolean didSomethingChange(){
			return somethingChanged;
		}
		
		private void SomethingChanged(){
			somethingChanged = true;
		}
		private boolean isBitSet( cfg.CFGBlock theNode ){
			Integer index = optParamBlock.dfnum.get( theNode );
			return theBits.get( index );
		}
	
		protected void NewTraversal(){
			theBits.clear();
		}
		
		//the following three data structures define all about expressions in the program. Since we are in SSA, we can 
		//go easy on kill sets and ignore them,
		private HashMap< String, Integer > inverseMap = new HashMap< String, Integer >();
		private ArrayList< String > expSet = new ArrayList< String >();
		private HashMap< String, HashMap< cfg.CFGBlock, InterRep.CodeBlock > > defLocations = new HashMap< String, HashMap< cfg.CFGBlock, InterRep.CodeBlock > >();
		private HashMap< String, HashMap< cfg.CFGBlock, InterRep.CodeBlock > > inheritedCode = new HashMap< String, HashMap< cfg.CFGBlock, InterRep.CodeBlock > >();
		private boolean IsKeyPresent( String key ){
			return inverseMap.containsKey( key );
		}
		private int InsertKey( String key, cfg.CFGBlock theNode, InterRep.CodeBlock theCodeBlock ){
			if( IsKeyPresent( key ) ){
				HashMap< cfg.CFGBlock, InterRep.CodeBlock > theLocs = defLocations.get( key );
				if( !theLocs.containsKey( theNode ) ){
					theLocs.put( theNode, theCodeBlock );
					defLocations.put( key, theLocs );
				}
				return inverseMap.get( key );
			}
			expSet.add( key );
			inverseMap.put( key, expSet.size() - 1 );
			HashMap< cfg.CFGBlock, InterRep.CodeBlock > temp = new HashMap< cfg.CFGBlock, InterRep.CodeBlock >();
			temp.put( theNode, theCodeBlock );
			defLocations.put( key, temp );
			return expSet.size() - 1;
			
		}
		
		private void RemoveInheritedCode( cfg.CFGBlock parent, cfg.CFGBlock current ){
			//if( this.inheritedCode.g)
			BitSet union = ( BitSet )this.defSet.get( parent ).clone();
			union.or( this.avblSet.get( parent ) );
			BitSet difference = ( BitSet ) this.avblSet.get( current ).clone();
			difference.andNot( union );
			if( difference.equals( this.avblSet.get( current ) ) ) return; 
			for( int i = difference.nextSetBit( 0 ); i >= 0 && i < expSet.size(); i = difference.nextSetBit( i+1 ) ) {
				String canonExp = this.expSet.get( i );
				HashMap< cfg.CFGBlock, InterRep.CodeBlock > inheritedLocs = this.inheritedCode.get( canonExp );
				if( inheritedLocs != null && inheritedLocs.containsKey( current ) ){
					inheritedLocs.remove( current );
				}
			}
		}
		private InterRep.CodeBlock returnCodeBlockForExpression( String canonExp, cfg.CFGBlock theNode ){
			HashMap< cfg.CFGBlock, InterRep.CodeBlock > inheritedLocs = this.inheritedCode.get( canonExp );
			if( inheritedLocs != null && inheritedLocs.containsKey( theNode ) ) return inheritedLocs.get( theNode );
			HashMap< cfg.CFGBlock, InterRep.CodeBlock > defLocs = this.defLocations.get( canonExp );
			if( defLocs != null && defLocs.containsKey( theNode ) ) return defLocs.get( theNode );
			
			return null;
		}
		private void InsertInheritedCode( cfg.CFGBlock parent, cfg.CFGBlock current ){
			BitSet bs = this.avblSet.get( current );
			for( int i = bs.nextSetBit( 0 ); i >= 0 && i < expSet.size(); i = bs.nextSetBit( i+1 ) ){
				String canonExp = this.expSet.get( i );
				HashMap< cfg.CFGBlock, InterRep.CodeBlock > defLocs = this.defLocations.get( canonExp );
				HashMap< cfg.CFGBlock, InterRep.CodeBlock > inheritedLocs = this.inheritedCode.get( canonExp );
			//	if( defLocs != null && defLocs.containsKey( current ) )continue;
				
				//now the hard part.
				InterRep.CodeBlock parentCode = null;
				if( defLocs != null && defLocs.containsKey( parent ) ){
					parentCode = defLocs.get( parent );
				}
				else{
					//we can crash here because inherited locs is supposed to contain parentcode.
					if( inheritedLocs == null && defLocs != null && defLocs.containsKey( current ) ) continue;
					parentCode = inheritedLocs.get( parent );
				}
				
				if( inheritedLocs != null && inheritedLocs.containsKey( current ) ){
					//we will remove currently inserted code and add a phi function instead.
					InterRep.CodeBlock currentlyInserted = inheritedLocs.remove( current );
					if( parentCode == currentlyInserted ){
						inheritedLocs.put( current, parentCode ); //skanky but will work 
						this.inheritedCode.put( canonExp, inheritedLocs );
						continue;
					}
					String varname = null;
					if( currentlyInserted.opCode != InterRep.CodeBlock.kPHI ){
						//yeah back to adobe days
						varname = parentCode.outputTemporary.serializeMe() ;
						currentlyInserted = current.AddPhiFunction( varname );
						varname = current.MakeOutputTempUnique( varname );
						this.SomethingChanged();
					}
					else{
						varname = currentlyInserted.outputTemporary.serializeMe();
					}
					
					InterRep.FrameInfo outputTemp = parentCode.outputTemporary;
					currentlyInserted = current.RenameJthPhiOperand( varname, parent, outputTemp );
					inheritedLocs.put( current, currentlyInserted );
					this.inheritedCode.put( canonExp, inheritedLocs );
					continue;
				}
				//need to handle the case where the element has more than 1 parent
				ArrayList< cfg.CFGBlock > predList = current.PredecessorList();
				if( 1 < predList.size() && this.defSet.get( current ).get( i ) ){
					//need to create a phi block in this case.
					String varname = parentCode.outputTemporary.serializeMe();
					InterRep.CodeBlock currentlyInserted = current.AddPhiFunction( varname );
					varname = current.MakeOutputTempUnique( varname );
					currentlyInserted = current.RenameJthPhiOperand( varname, parent, parentCode.outputTemporary );
					parentCode = currentlyInserted;
					
				}
				if( inheritedLocs != null ){
					inheritedLocs.put( current, parentCode );
					this.inheritedCode.put( canonExp, inheritedLocs );
					continue;
				}
				
				inheritedLocs = new HashMap< cfg.CFGBlock, InterRep.CodeBlock >();
				inheritedLocs.put( current, parentCode );
				this.inheritedCode.put( canonExp, inheritedLocs );
			}
		}
		//the defn set and the set that is exposed by the predecessors of each cfgblock.
		private HashMap< cfg.CFGBlock, BitSet > defSet = new HashMap< cfg.CFGBlock, BitSet >();
		private HashMap< cfg.CFGBlock, BitSet > avblSet = new HashMap< cfg.CFGBlock, BitSet >();
		
		public CommonSubexpressionElimination( cfg.OPTParamBlock paramBlock){
			super();
			optParamBlock = paramBlock;
			theBits = new BitSet( optParamBlock.vertex.size() );
		}
		
		protected boolean Process( cfg.CFGBlock currentVisited, cfg.CFGBlock theParent ){
			
			if( null == theParent ){
				this.SetVisitedBit( currentVisited );
				return true;
			}
			if( currentVisited.BlockLabel().equals("foo1:7" ) ){
				boolean a = true;
			}
			this.RemoveInheritedCode( theParent, currentVisited );
			BitSet cloned = null;
			boolean alreadyVisited = false;
			BitSet sectSet = this.avblSet.get( currentVisited );
			cloned = ( BitSet )sectSet.clone();
			if( this.isBitSet( currentVisited ) ){
				alreadyVisited = true;
			}
			this.SetVisitedBit( currentVisited );
			BitSet unionSet = ( BitSet )this.avblSet.get( theParent ).clone();
			unionSet.or( this.defSet.get( theParent ) );
			sectSet.and( unionSet );
			this.avblSet.put( currentVisited, sectSet );
			boolean equals = sectSet.equals( cloned );
			this.InsertInheritedCode( theParent, currentVisited );
			if( alreadyVisited && !equals ){
				super.Process( currentVisited, theParent );
				return false;
			}
			else if( alreadyVisited ){
				return false;
			}
			
			return true;
		}
		protected void PostProcess( cfg.CFGBlock theRoot ){
			for( cfg.CFGBlock theVertex : optParamBlock.vertex ){
				//HashMap< Integer>
				ArrayList< InterRep.CodeBlock > stmList = theVertex.GetStatementsList();
				int sz = stmList.size();
				for( int i = 0; i < sz; ++i ){
					InterRep.CodeBlock stm = stmList.get( i );
					String canonExp = stm.returnCanonicalName();
					if( null == canonExp ) continue;
					InterRep.FrameInfo fm = stm.outputTemporary;
					InterRep.CodeBlock inherited = this.returnCodeBlockForExpression( canonExp, theVertex );
					//it will crash let it thats how i can catch bugs in java
					//in java world everything is possible java rocks lol
					if( null != inherited && inherited == stm ) continue; //first defn.
				//	if( null == inherited ) continue;
					InterRep.FrameInfo src  = inherited.outputTemporary;
					InterRep.CodeBlock movStm = InterRep.CodeBlock.generateMoveOrStoreOP( src, fm, InterRep.CodeBlock.kMOVE );
					if( movStm.label.equals("main:112") ){
						boolean a = true;
					}
					InterRep.CodeBlock cdPrev = stmList.get( i );
					movStm.label = new String( cdPrev.label );
					stmList.set( i, movStm );
					stmList.get( i ).ResetCache(); //really hacky but i am proud of it!!
					this.SomethingChanged();
				}
			}
		}
		protected void PreProcess( cfg.CFGBlock theRoot ){
			//root is ignored here.
			//we build all the expression set; set up initial mapping and initial the various deflists here
			ArrayList< ArrayList< Integer > > tempIndices = new ArrayList< ArrayList< Integer > >();
			for( cfg.CFGBlock theVertex : optParamBlock.vertex ){
				ArrayList< Integer > blockIndices = new ArrayList< Integer >();
				for( InterRep.CodeBlock cd : theVertex.GetStatementsList() ){
					String theStmt = cd.returnCanonicalName();
					if( null == theStmt ) continue;
					//we in all likelyhood have a valid expression here
					blockIndices.add( InsertKey( theStmt, theVertex, cd ) );
				}
				tempIndices.add( blockIndices );
			}
			int sz = optParamBlock.vertex.size();
			for( int i = 0; i < sz; ++i ){
				cfg.CFGBlock theVertex = optParamBlock.vertex.get( i );
				ArrayList< Integer > blockIndex = tempIndices.get( i );
				BitSet curDefSet = new BitSet( expSet.size() );
				curDefSet.set( 0, expSet.size(), false );
				BitSet curAvblSet = new BitSet( expSet.size() );
				curAvblSet.set( 0, expSet.size() );
				
				for( Integer curInd : blockIndex ){
					curDefSet.set( curInd );
				}
				
				this.defSet.put( theVertex, curDefSet );
				this.avblSet.put( theVertex, curAvblSet );
			}
			
			this.avblSet.get( optParamBlock.root ).clear();
			
		}
	}
	
public static class CopyPropagation extends ForwardOptimizer{
	private ArrayList< String > moveSet = new ArrayList< String >();
	private HashMap< String, Integer > inverseMap = new HashMap< String, Integer >();
	private HashMap< String, String > killedList = new HashMap< String, String >();
	private HashMap< cfg.CFGBlock, HashMap< String, String > > keyValueDefs = new HashMap< cfg.CFGBlock, HashMap< String, String > >();
	private ArrayList< String > varsInScope = null; 
	private void ComposeFromOneParent( cfg.CFGBlock currentVisited, cfg.CFGBlock currentParent ){
		if( !keyValueDefs.containsKey( currentParent ) ){
			boolean a = true; //should use exceptions here
			return;
		}
		
		HashMap< String, String > keyVal = keyValueDefs.get( currentParent );
		//HashMap< String, String > childKeyVal = keyVal.cl
		HashMap< String, String > cloned = new HashMap< String, String >();
		Set< String > keySet = keyVal.keySet();
		for( String key : keySet ){
			String val = keyVal.get( key );
			String newKey = new String( key );
			String newVal = new String( val );
			assert !cloned.containsKey( newKey );
			cloned.put( newKey, newVal );
		}
		
		killedList = cloned;
	}
	private void ComposeFromAllParents( cfg.CFGBlock currentVisited ){
		HashMap< String, InterRep.CodeBlock > phiFuncs = currentVisited.returnPhiFunctions();
		HashMap< String, String > keyVal = new HashMap< String, String >();
		Set< String > phiVars = phiFuncs.keySet();
		for( String var : phiVars ){
			InterRep.CodeBlock phiBlock = phiFuncs.get( var );
			String varname = phiBlock.outputTemporary.serializeMe();
			if( this.varsInScope.contains( var ) ){
				keyVal.put( new String( var ), new String( varname ) );
			}
		}
		//pick some random predecessor and fill up the rest.
		cfg.CFGBlock randomPred = null;//currentVisited.PredecessorList().get( 0 );
		for( cfg.CFGBlock rand : currentVisited.PredecessorList() ){
			if( rand.isDeleted ) continue;
			randomPred = rand;
			break;
		}
	//	assert randomPred != null;
		if( null == randomPred ){
			for( String var : this.varsInScope ){
				if( !keyVal.containsKey( var ) ){
					keyVal.put( new String( var ), new String( var ) );
				}
			}
		}
		else{
			HashMap< String, String > predMap = this.keyValueDefs.get( randomPred );
			Set< String > varSet = predMap.keySet();
			for( String key : varSet ){
				if( !keyVal.containsKey( key ) ){
					String val = predMap.get( key );
					keyVal.put( new String( key ), new String( val ) );
				}
			}	
		}
		//now update the running list.
		this.killedList = keyVal;
	}
	
	private void UpdateFromInstruction( InterRep.CodeBlock cdBlk ){
		InterRep.FrameInfo opTemp = cdBlk.outputTemporary;
		if( null == opTemp ) return;
		String opName = opTemp.returnRValueTemporary();
		if( null == opName || opName.isEmpty() ) return;
		String opValue = opTemp.serializeMe();
		if( !this.killedList.containsKey( opName ) ) return;
		this.killedList.put( opName, opValue );
	}
	
	private void Commit( cfg.CFGBlock currentVisited ){
		assert !killedList.isEmpty();
		HashMap keyVal = new HashMap< String, String >();
		Set< String > keySet = killedList.keySet();
		for( String key : keySet ){
			String val = killedList.get( key );
		//	assert !keyVal.containsKey( key );
			String newKey = new String( key );
			String newVal = new String( val );
			keyVal.put( newKey, newVal );
		}
		this.keyValueDefs.put( currentVisited, keyVal );
	}
	private boolean somethingChanged = false;
	public boolean didSomethingChange(){
		return somethingChanged;
	}
	
	private void SomethingChanged(){
		somethingChanged = true;
	}
	private int InsertMoveStmt( String phiStmt ){
		moveSet.add( phiStmt );
		inverseMap.put( phiStmt, moveSet.size() - 1 );
		return moveSet.size() - 1;
	}
	private cfg.OPTParamBlock optParamBlock = null;
	private BitSet theBits = new BitSet( );
	private void SetVisitedBit( cfg.CFGBlock theNode ){
		Integer index = optParamBlock.dfnum.get( theNode );
		theBits.set( index );
	}
	
	private boolean isBitSet( cfg.CFGBlock theNode ){
		Integer index = optParamBlock.dfnum.get( theNode );
		return theBits.get( index );
	}

	private HashMap< cfg.CFGBlock, BitSet > defSet = new HashMap< cfg.CFGBlock, BitSet >();
	private HashMap< cfg.CFGBlock, BitSet > avblSet = new HashMap< cfg.CFGBlock, BitSet >();
	private HashMap< String, InterRep.FrameInfo > replacements = new HashMap< String, InterRep.FrameInfo >();
	private void InsertIntoReplacements( String key, InterRep.FrameInfo val ){
		if( replacements.containsKey( key ) || key.contains("RETURN") ){
			boolean a = true;
			return;
		}
		replacements.put( key, val );
	}
	protected void NewTraversal(){
		theBits.clear();
	}
	
	public CopyPropagation( cfg.OPTParamBlock theParams ){
		super();
		optParamBlock = theParams;
		theBits = new BitSet( optParamBlock.vertex.size() );
	}
	
	private boolean IsValidMove( InterRep.CodeBlock theCdBlk ){
		return theCdBlk.returnMovCanonicalName() != null && !theCdBlk.IsReturnOp() && !theCdBlk.isArgPassingStatement && theCdBlk.opCode != theCdBlk.kPHI && InterRep.globalSymTab.IsSafeForOptimize( theCdBlk );
	}
	
	protected void PreProcess( cfg.CFGBlock theRoot ){
		//get the variables and initialize key defs for the root alone
		String optScope = InterRep.globalSymTab.GetOptimizeScope();
		InterRep.VarDecl theDecls = InterRep.globalSymTab.getVarDeclInfo( optScope );
		ArrayList< String > varIdentList = theDecls.mIdentList;
		varsInScope = varIdentList;
		HashMap< String, String > keyVal = new HashMap< String, String >();
		for( String var : varIdentList ){
			String key = new String( var );
			String val = new String( var );
			if( keyVal.containsKey( key ) ){
				boolean a = true;
			}
			keyVal.put( key, val );
		}
		this.keyValueDefs.put( theRoot, keyVal );
		ArrayList< ArrayList< Integer > > tempIndices = new ArrayList< ArrayList< Integer > >();
		for( cfg.CFGBlock curNode : optParamBlock.vertex ){
			ArrayList< Integer > blockIndices = new ArrayList< Integer >();
			HashMap< String, InterRep.CodeBlock > phiList = new HashMap< String, InterRep.CodeBlock  >(); 
			phiList = curNode.returnPhiFunctions();
			for( String varname : phiList.keySet() ){
				InterRep.CodeBlock phiBlock = phiList.get( varname );
				String movStmt = phiBlock.returnMovCanonicalName();
				if( null == movStmt ) continue;
				InsertMoveStmt( movStmt );
			}
			
			ArrayList< InterRep.CodeBlock > cdList = curNode.GetStatementsList();
			for( int i = 0; i < cdList.size(); ++i ){
				InterRep.CodeBlock stmt = cdList.get( i );
				String movStmt = stmt.returnMovCanonicalName();
				if( null == movStmt ){
					if( stmt.label.equals("main:29") ){
						boolean a = true;
					}
					InterRep.CodeBlock mvBlock = stmt.EvaluateOperandsIfConstant();
					if( null != mvBlock && this.IsValidMove( mvBlock ) ){
						cdList.set( i, mvBlock );
						stmt = mvBlock;
						movStmt = stmt.returnMovCanonicalName();
					}
				}
				if( null == movStmt || !this.IsValidMove( stmt ) ) continue;
				blockIndices.add( InsertMoveStmt( movStmt ) );
				this.InsertIntoReplacements( stmt.returnLVALOperand(), stmt.returnMovOperand() );
			}
			tempIndices.add( blockIndices );
		}
		
		int sz = optParamBlock.vertex.size();
		for( int i = 0; i < sz; ++i ){
			ArrayList< Integer > blockIndices = tempIndices.get( i );
			cfg.CFGBlock curVertex = optParamBlock.vertex.get( i );
			BitSet curDefSet = new BitSet( this.moveSet.size() );
			curDefSet.clear();
			for( Integer indx : blockIndices ){
				curDefSet.set( indx );
			}
			BitSet curAvblSet = new BitSet( this.moveSet.size() );
			curAvblSet.set( 0, this.moveSet.size(), true );
			
			this.defSet.put( curVertex, curDefSet );
			this.avblSet.put( curVertex, curAvblSet );
		}
		
		this.avblSet.get( optParamBlock.root ).clear();
	}

	private boolean CreateNewMoves( cfg.CFGBlock currentVisited ){
		ArrayList< InterRep.CodeBlock > theCdList = currentVisited.GetStatementsList();
		boolean inserted = false;
		for( int i = 0; i < theCdList.size(); ++i ){
			InterRep.CodeBlock theCdBlk = theCdList.get( i );
			InterRep.CodeBlock nextBlk = null;
			if( i < theCdList.size() - 1 ){
				nextBlk = theCdList.get( i + 1);
			}
			if( this.IsValidMove( theCdBlk ) ){
				this.UpdateFromInstruction( theCdBlk );
				continue;
			}
			theCdBlk.ReplaceOperands( replacements, killedList );
			if( theCdBlk.IsConstantCompare() && null != nextBlk && nextBlk.IsCondBra() ){
				boolean taken = theCdBlk.PerformComparison( nextBlk );
				ArrayList< cfg.CFGBlock > succList = currentVisited.SuccessorList();
				if( 2 == succList.size() ){
					theCdBlk.isDeleted = true;
					nextBlk.isDeleted = true;
					++i;
					String label = nextBlk.jumpLabel;
					cfg.CFGBlock blockToDelete = null;
					for( cfg.CFGBlock blk : succList ){
						if( blk.BlockLabel().equals( label ) && !taken ){
							blockToDelete = blk;
						}
						else if( !blk.BlockLabel().equals( label ) && taken ){
							blockToDelete = blk;
						}
					}
					boolean temp = blockToDelete.DeleteEdge( currentVisited, replacements, nodeQueue );
					inserted = inserted || temp;
					if( inserted ) SomethingChanged();
					continue;
				}
			}
			InterRep.CodeBlock theMv  = theCdBlk.EvaluateOperandsIfConstant();
			if( theCdBlk.label.equals("main:29") ){
				boolean a = true;
			}
			if( null != theMv && this.IsValidMove( theMv ) ){
				theCdList.set( i, theMv );
				SomethingChanged();
				this.InsertIntoReplacements( theMv.returnLVALOperand(), theMv.returnMovOperand() );
				this.UpdateFromInstruction( theMv );
				inserted = true;
			}
			else{
				this.UpdateFromInstruction( theCdBlk );
			}
		}
		return inserted;
	}
	
	protected boolean Process( cfg.CFGBlock currentVisited, cfg.CFGBlock theParent ){
		
		this.EnsureNotPresent( currentVisited );
		if( null == theParent ){
			this.SetVisitedBit( currentVisited );
			return true;
		}
		
		
		if( currentVisited.isDeleted ){
			optParamBlock.dfnum.remove( currentVisited );
			optParamBlock.vertex.remove( currentVisited );
			return false;
		}
		
		//first create the kill set for this block.
		this.ComposeFromOneParent( currentVisited, theParent );
		
		BitSet cloned = null;
		boolean alreadyVisited = false;
		BitSet sectSet = this.avblSet.get( currentVisited );
		cloned = ( BitSet )sectSet.clone();
		if( this.isBitSet( currentVisited ) ){
			alreadyVisited = true;
		}
		this.SetVisitedBit( currentVisited );
		BitSet unionSet = ( BitSet )this.avblSet.get( theParent ).clone();
		boolean notEquals = false;
		if( currentVisited.PredecessorList().size() == 1 )unionSet.or( this.defSet.get( theParent ) );
		else{
			//as a side effect this updates the kill set
			notEquals = this.UpdatePhi( currentVisited, theParent );
		}
		sectSet.and( unionSet );
		this.avblSet.put( currentVisited, sectSet );
		notEquals = notEquals || !sectSet.equals( cloned );
		boolean didcreate = this.CreateNewMoves( currentVisited );
		notEquals = notEquals || didcreate;
		//commit the killed set for the current node.
		this.Commit( currentVisited );
		if( alreadyVisited && notEquals ){
			super.Process( currentVisited, theParent );
			return false;
		}
		else if( alreadyVisited ){
			return false;
		}
		
		return true;
	}
	
	private boolean UpdatePhi( cfg.CFGBlock currentVisited, cfg.CFGBlock theParent ){
		int indx = currentVisited.jthPredecessor( theParent );
		HashMap< String, InterRep.CodeBlock > thePhiList = currentVisited.returnPhiFunctions();
		boolean didInsert = false;
		InterRep.FrameInfo fmTemp = null;
		for( String varname : thePhiList.keySet() ){
			InterRep.CodeBlock cdBlk = thePhiList.get( varname );
			if( cdBlk.isDeleted ) continue;
			cdBlk.ReplaceOperand( this.replacements, indx, killedList );
			boolean areAllEqual = cdBlk.AllOperandsSame();
			if( areAllEqual ){
				InterRep.FrameInfo fm = cdBlk.returnMovOperand();
				String str = cdBlk.returnLVALOperand();
				this.replacements.put( str, fm );
				cdBlk.isDeleted = true;
				SomethingChanged();
			}
			/*else if( ( fmTemp = cdBlk.PhiAllButOneSame() ) !=  null ){
				areAllEqual = true;
				String str = cdBlk.returnLVALOperand();
				this.replacements.put( str, fmTemp );
				cdBlk.isDeleted = true;
				SomethingChanged();
			}*/
			didInsert = didInsert || areAllEqual;
			//now update the kill set
			this.UpdateFromInstruction( cdBlk );
		}
		
		return didInsert;
	}
	
	protected void PostProcess( cfg.CFGBlock theRoot ){
		for( cfg.CFGBlock theVertex : this.optParamBlock.vertex ){
			if( theVertex.BlockLabel().equals("ROOT") ) continue;
			this.ComposeFromAllParents( theVertex );
			for( InterRep.CodeBlock theCdBlk : theVertex.GetStatementsList() ){
				if( this.IsValidMove( theCdBlk ) ){
					theCdBlk.isDeleted = true;
					continue;
				}
				else if( theCdBlk.opCode == InterRep.CodeBlock.kMOVE ){
					theCdBlk.ReplaceMovOperands( replacements, killedList );
					continue;
				}
				theCdBlk.ReplaceOperands( replacements, killedList );
				theCdBlk.ResetCache();
			}
		}
		
		ArrayList< cfg.CFGBlock > deletedBlocks = new ArrayList< cfg.CFGBlock >();
		Set< cfg.CFGBlock > keysets = this.optParamBlock.dfnum.keySet();
		for( cfg.CFGBlock curBlock : keysets ){
			if( curBlock.IsEmpty() && curBlock != optParamBlock.root || curBlock.isDeleted ){
				curBlock.DeleteNode();
				deletedBlocks.add( curBlock );
			}
			/*else{
				curBlock.FixupPredLabel();
			}*/
		}
		for( cfg.CFGBlock blk : deletedBlocks ){
			optParamBlock.dfnum.remove( blk );
			optParamBlock.vertex.remove( blk );
		}
		/*for( int i = optParamBlock.vertex.size() - 1; i >= 0 ; --i ){
			cfg.CFGBlock theVertex = optParamBlock.vertex.get( i );
			theVertex.ReplaceJumpLabelsOfPred();
		}*/
	}
}
}

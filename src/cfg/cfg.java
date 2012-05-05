package cfg;
import intermediateObjects.InterRep.*;

import java.io.*;

import java.util.*;

import com.sun.net.httpserver.HttpHandler;
import registerAlloc.RegisterAllocator.*;

public class cfg {
	private static HashMap< String, CFGBlock > cfgForest = new HashMap< String, CFGBlock >();
	public static class OPTParamBlock{
		public HashMap< CFGBlock, Integer > dfnum = new HashMap< CFGBlock, Integer >();
		public ArrayList< CFGBlock > vertex = new ArrayList< CFGBlock >();
		public CFGBlock root = new CFGBlock();
		OPTParamBlock( HashMap< CFGBlock, Integer > theDFNum, ArrayList< CFGBlock > theVertex, CFGBlock theRoot ){
			dfnum = theDFNum;
			vertex = theVertex;
			root = theRoot;
		}
	}
	
	public static class TopologicalSort{
		private ArrayList< CFGBlock > mSortedList = new ArrayList< CFGBlock> ();
		private HashMap< CFGBlock, Integer > mPos = new HashMap< CFGBlock, Integer >();
		private boolean mIsSorted = false;
		private CFGBlock mRoot = null;
		private HashSet< CFGBlock > mVisitedSet = new HashSet< CFGBlock >();
		public TopologicalSort( CFGBlock root ){
			super();
			mRoot = root;
		}
		
		private void AdjustMPos(){
			Set< CFGBlock > keySet = mPos.keySet();
			for( CFGBlock key : keySet ){
				Integer val = mPos.get( key );
				val++;
				mPos.put( key, val );
			}
		}
		private void TraverseNode( CFGBlock node ){
			if( mVisitedSet.contains( node ) ){
				return;
			}
			mVisitedSet.add( node );
			//ArrayList< CFGBlock > orderedSucc = new ArrayList< CFGBlock >();
			CFGBlock inorderSucc = null;
			CFGBlock branchSucc = null;
			for( CFGBlock succ : node.SuccessorList() ){
				//TraverseNode( succ );
				//if( node.BlockLabel().equals(succ.))
				if( succ.BlockLabel().equals( node.JumpLabel() ) ){
					branchSucc = succ;
				}
				else{
					inorderSucc = succ;
				}
			}
			if( null != branchSucc )
				TraverseNode( branchSucc );
			if( null != inorderSucc )
				TraverseNode( inorderSucc );
			//ArrayList< CFGBlock > succList = node.SuccessorList()
			if( mSortedList.isEmpty() ){
				mSortedList.add( node );
				//mPos.put( node, 0 );
			}
			else{
				//AdjustMPos();
				if( null != inorderSucc && mSortedList.get( 0 ) != inorderSucc ){
					//add an uncond bra to inorder succ.
					node.AddUncondBra( inorderSucc );
				}
				mSortedList.add( 0, node );
				//mPos.put( node, 0 );
			}
			
		}
		private void Sort(){
			TraverseNode( mRoot );
		}
		public ArrayList< CFGBlock > ReturnSorted(){
			if( !mIsSorted ){
				Sort();
				mIsSorted = true;
			}
			return mSortedList;
		}
	}
	public static class DFSTraverse{
		protected HashMap< CFGBlock, Integer > dfnum = new HashMap< CFGBlock, Integer >();
		protected ArrayList< CFGBlock > vertex = new ArrayList< CFGBlock >();
		protected HashMap< CFGBlock, CFGBlock > parent = new HashMap< CFGBlock, CFGBlock >();
		protected HashMap< CFGBlock, CFGBlock > semi = new HashMap< CFGBlock, CFGBlock >();
		protected HashMap< CFGBlock, CFGBlock > label = new HashMap< CFGBlock, CFGBlock >();
		protected static int N = 0;
		private boolean printTree = false;
		public DFSTraverse(){
			super();
			N = 0;
		}
		public DFSTraverse( boolean print ){
			printTree = print;
			N = 0;
		}
		public void DFS( CFGBlock p, CFGBlock current ){
			if( dfnum.containsKey( current ) == false ){
				dfnum.put( current, N );
				vertex.add( current );
				semi.put( current, current );
				label.put( current, current );
				parent.put( current, p );
				if( printTree )
					current.printMe();
				N++;
				ArrayList< CFGBlock > succList = current.SuccessorList();
				for( int i = 0; i < succList.size(); ++i ) {
					CFGBlock succ = succList.get( i );
					DFS( current, succ );
				}
			}	
		}
		
		public void printBFSTree( CFGBlock current ){
			Integer N =1;
			Integer Level = 0;
			ArrayList <CFGBlock > BFSQueue = new ArrayList< CFGBlock >();
			BFSQueue.add( current );
			while(!BFSQueue.isEmpty() ){
				CFGBlock theElem = BFSQueue.remove( 0 );
				System.out.print( "Tree Traversal Level "+ Level + "Node Number" + N++ );
				theElem.printMe();
				for( CFGBlock child : theElem.GetDomChildren() ){
					BFSQueue.add( child );
				}
				Level++;
			}
		}
	}
	public static class Dominator extends DFSTraverse{
		public Dominator(){
			super();
		}
		protected HashMap< CFGBlock, ArrayList< CFGBlock > > bucket = new HashMap< CFGBlock, ArrayList< CFGBlock > >();
		
		protected HashMap< CFGBlock, CFGBlock > ancestor = new HashMap< CFGBlock, CFGBlock >();
		protected HashMap< CFGBlock, CFGBlock > idom = new HashMap< CFGBlock, CFGBlock >();
		protected HashMap< CFGBlock, CFGBlock > samedom = new HashMap< CFGBlock, CFGBlock >();
		protected HashMap< CFGBlock, ArrayList< CFGBlock > > dominanceFrontier = new HashMap< CFGBlock, ArrayList< CFGBlock > >();
		protected HashMap< String, ArrayList< CFGBlock > > defSites = new HashMap< String, ArrayList< CFGBlock > >();
		protected HashMap< String, Integer > Count = new HashMap< String, Integer >();
		protected HashMap< String, ArrayList< Integer > > stack = new HashMap< String, ArrayList< Integer > >();
		private static String BuildNode( CFGBlock cs, int link, Dominator values ){
			String node = "node: {\n";
			node += "title: \"" + cs.BlockLabel() + "\"\n";
			node += "label: \"" + cs.BlockLabel() + "[\n";
			for( CodeBlock phiSet : cs.returnPhiFunctions().values() ){
				node += CodeBlock.serializeMe( phiSet );
			//	node += "\n";
			}
			
			for( CodeBlock stmt : cs.GetStatementsList() ){
				node += CodeBlock.serializeMe( stmt );
			}
			
			node += "]\"\n}\n";
			ArrayList< CFGBlock > succList = new ArrayList< CFGBlock >();
			if( link == 1 ) succList = cs.GetDomChildren();
			else if( link == 0 )succList = cs.SuccessorList();
			else if( 2 == link && null != values ){
				HashMap< CFGBlock, ArrayList< CFGBlock > > dmFront = values.dominanceFrontier;
				succList = dmFront.get( cs );
			}
			for( CFGBlock succ : succList ){
				node += "edge: { sourcename: \"" + cs.BlockLabel() + "\"\n";
				node += "targetname: \"" + succ.BlockLabel() + "\"\n";
				node += "color: blue\n}\n";
			}
			return node;		
		}
		public static void DumpToVCG( String filename, CFGBlock root, int link, Dominator values ){
			Dominator theDom = new Dominator();
			if( values == null ){
				theDom.DFS( null, root );
			}
			
			try {
				BufferedWriter writer = null;
			    writer = new BufferedWriter( new FileWriter( filename ) );
			    String header = "graph: { title: \"Control Flow Graph\"\nlayoutalgorithm: dfs\nmanhattan_edges: yes\nsmanhattan_edges: yes\n";
			    ArrayList<CFGBlock> blks = new ArrayList< CFGBlock >();
			    if( values != null ) blks = values.vertex;
			    else blks = theDom.vertex;
			    for( CFGBlock c : blks ){
			    	header += BuildNode( c, link, values );
			    }
			    header += "}\n";
			    
			    writer.write( header );
			    writer.close();
			} catch (IOException e) {
			}
		}
		private void AddToDefSites( String var, CFGBlock blk ){
			if( defSites.containsKey( var ) ){
				defSites.get( var ).add( blk );
				return;
			}
			ArrayList< CFGBlock > temp = new ArrayList< CFGBlock >();
			temp.add( blk );
			defSites.put( var, temp );
		}
		private void AddToStack( String var ){
			if( this.Count.containsKey( var ) ){
				Integer val = this.Count.get( var );
				val++;
				this.Count.put( var, val );
				this.stack.get( var ).add( val );
				return;
			}
			ArrayList< Integer > temp = new ArrayList< Integer >();
			temp.add( 0 );
			stack.put( var, temp );	
			this.Count.put( var, 0 );
		}
		private String GetLastEntryInStack( String var ){
			if( var.contains( "$RETURN" ) || !stack.containsKey( var ) ){
				return var;
			}
			ArrayList< Integer > temp =  stack.get( var );
			if( temp.isEmpty() ) return var;
			int val = temp.get( temp.size() - 1 );
			if( 0 == val ) return var;
			return var + "_" + String.valueOf( val );
		}
		
		private void RemoveLastEntryInStack( String var ){
			if( !this.stack.containsKey( var ) ) return;
			ArrayList< Integer > temp = stack.get( var );
			int val =  temp.get( temp.size() - 1 );
			//--val;
			//this.Count.put( var, val );
			temp.remove( temp.size() - 1 );
		}
		private void AddToBucket( CFGBlock bucketKey, CFGBlock bucketVal ){
			if( bucket.containsKey( bucketKey ) ){
				bucket.get( bucketKey ).add( bucketVal ); 
				return;
			}
			ArrayList< CFGBlock > temp = new ArrayList< CFGBlock >();
			temp.add( bucketVal );
			bucket.put( bucketKey, temp );
		}
		
		private void ClearBucket( CFGBlock bucketKey ){
			if( bucket.containsKey( bucketKey ) ){
				bucket.get( bucketKey ).clear();
			}
		}
		
		private CFGBlock AncestorWithLowestSemi1( CFGBlock thePred ){
			CFGBlock anc = ancestor.get( thePred );
			if( null != anc ){
				CFGBlock b = AncestorWithLowestSemi1( anc );
				ancestor.put( thePred, ancestor.get( anc ) );
				if( this.dfnum.get( this.semi.get( b ) ) < this.dfnum.get( this.semi.get( this.label.get( thePred ) ) ) ){
					label.put( thePred, b );
				}
			}
			return label.get( thePred );
		}
		
		private void Link( CFGBlock parent, CFGBlock node ){
			ancestor.put( node, parent ); 
			//label.put( node, node );
		}
		public CFGBlock BuildDominanceFrontier( CFGBlock rootNode ){
			ArrayList< CFGBlock > currentDF = new ArrayList< CFGBlock >();
			for( CFGBlock y : rootNode.SuccessorList() ){
				if( this.idom.get( y ) != rootNode  ){
					currentDF.add( y );
				}
			}
			for( CFGBlock c : rootNode.GetDomChildren() ){
				BuildDominanceFrontier( c );
				for( CFGBlock w : this.dominanceFrontier.get( c  ) ){
					if( !IsDominated( rootNode, w ) && !currentDF.contains( w ) ){
						currentDF.add( w );
					}
				}
			}
			this.dominanceFrontier.put( rootNode, currentDF );
			return rootNode;
		}
		
		public CFGBlock InsertPhiFuncBlock(){
			
			for( CFGBlock n : vertex ){
				for( String a : n.returnVars() ){
					this.AddToDefSites( a, n );
				}
			}
			
			for( String a : this.defSites.keySet() ){
				ArrayList< CFGBlock > W = this.defSites.get( a );
				while( !W.isEmpty() ){
					CFGBlock n = W.remove( 0 );
					for( CFGBlock y : this.dominanceFrontier.get( n ) ){
						y.AddPhiFunction( a );
						//Register Allocation
//						y.AddPhiInputBlock(n, a);
						if( !y.isVarDefined( a ) ){
							W.add( y );
							y.DefineVar( a );
						}
							
					}
				}
			}
			return vertex.get( 0 );
		}
		public void InitializeForRenaming( ){
			for( String a : intermediateObjects.InterRep.globalSymTab.getDeclListCurrent() ){
				this.AddToStack( a );
			}
		}
		public OPTParamBlock RenamePhiBlock( CFGBlock n ){

			//hack to fix a bug in which if a variable is not used in a path, and we reach a predecessor
			//which tries to rename the phi block in its successor.
			HashMap< String, CodeBlock > phiBlocks = n.returnPhiFunctions();
			for( String var : phiBlocks.keySet() ){
				CodeBlock S = phiBlocks.get( var );
				/*for( FrameInfo fm : S.operands ){
					if( fm instanceof ConstFrameInfo )
						continue;
					String x = intermediateObjects.InterRep.globalSymTab.variableName( fm ); 
					String xi =this.GetLastEntryInStack( x );
					intermediateObjects.InterRep.globalSymTab.ReplaceKey( x, xi, fm );
				}*/
				FrameInfo opTemp = S.outputTemporary;
				this.AddToStack( opTemp.tempID );
				String newVal = this.GetLastEntryInStack( opTemp.tempID );
				intermediateObjects.InterRep.globalSymTab.ReplaceKey( opTemp.tempID, newVal, opTemp );
			}
			for( CodeBlock S : n.GetStatementsList() ){
				for( FrameInfo fm : S.operands ){
					if( fm instanceof ConstFrameInfo )
						continue;
					String x = intermediateObjects.InterRep.globalSymTab.variableName( fm ); 
					String xi =this.GetLastEntryInStack( x );
					intermediateObjects.InterRep.globalSymTab.ReplaceKey( x, xi, fm );
				}
				//every statement has exactly one definition namely outputTemporary
				if( !S.isLetMoveStatement ) continue;
				FrameInfo opTemp = S.outputTemporary;
				this.AddToStack( opTemp.tempID );
				String newVal = this.GetLastEntryInStack( opTemp.tempID );
				intermediateObjects.InterRep.globalSymTab.ReplaceKey( opTemp.tempID, newVal, opTemp );
			}
			
			for( CFGBlock succ :  n.SuccessorList() ){
				int j = succ.jthPredecessor( n );
				ArrayList< CFGBlock > thePredList = succ.PredecessorList();
				if( thePredList.get( j ) == n ){
					HashMap< String, CodeBlock > phiFuncs =  succ.returnPhiFunctions();
					for(String varname : phiFuncs.keySet() ){
						CodeBlock phi = phiFuncs.get( varname );
						FrameInfo jthOperand = phi.operands.get( j );
						String xi = this.GetLastEntryInStack( varname );
						if( xi.equals("d_1") ){
							boolean a = true;
						}
						
						intermediateObjects.InterRep.globalSymTab.ReplaceKey( varname, xi, jthOperand );
						
					}
				}
			}
			for( CFGBlock child : n.GetDomChildren() ){
				this.RenamePhiBlock( child );
			}
			HashMap< String, CodeBlock > phiSet = n.returnPhiFunctions();
			for( String phiVar : phiSet.keySet() ){
				CodeBlock phi = phiSet.get( phiVar );
				String varname = intermediateObjects.InterRep.globalSymTab.variableName( phi.outputTemporary );
				this.RemoveLastEntryInStack( varname );
			}
			for( CodeBlock stmt : n.GetStatementsList() ){
				if( !stmt.isLetMoveStatement ) continue;
				
				String varname = intermediateObjects.InterRep.globalSymTab.variableName( stmt.outputTemporary );
				this.RemoveLastEntryInStack( varname );
			}
			return new OPTParamBlock( dfnum, vertex, n );
		}
		private boolean IsDominated( CFGBlock n, CFGBlock w ){
			if( w == n ) return false;
			while( w.GetDomParent() != null ){
				if( n == w.GetDomParent() )
					return true;
				w = w.GetDomParent();
			}
			return false;
		}
		public CFGBlock BuildDominatorTree( CFGBlock r ){
			CFGBlock rootNode = r;
			DFS( null, r );
			for( int i =  N - 1; i > 0; --i ){
				CFGBlock currentBlock = vertex.get( i );
				CFGBlock parentBlock = parent.get( currentBlock );
				CFGBlock potentialSemiDom = parentBlock;
				ArrayList< CFGBlock > predList = currentBlock.PredecessorList();
				ArrayList< CFGBlock > badPreds = new ArrayList< CFGBlock >();
				for( int j = 0; j < predList.size(); ++j ){
					CFGBlock thePred = predList.get( j );
					CFGBlock theBestSemiDom = null;
					if( !this.dfnum.containsKey( thePred ) ){
						badPreds.add( thePred );
						continue;
					}
					if( this.dfnum.get( thePred ) <= this.dfnum.get( currentBlock ) ) {
						theBestSemiDom = thePred;
					}
					else{
						theBestSemiDom = semi.get(AncestorWithLowestSemi1( thePred ));
					}
					if( this.dfnum.get( theBestSemiDom ) < this.dfnum.get( potentialSemiDom ) ){
						potentialSemiDom = theBestSemiDom;
					}
				}
				for( CFGBlock cur : badPreds ){
					predList.remove( cur );
				}
				this.semi.put( currentBlock, potentialSemiDom );
				this.AddToBucket( potentialSemiDom, currentBlock );
				this.Link( parentBlock , currentBlock );
				if( this.bucket.containsKey( parentBlock ) ){
					
					for (CFGBlock v : this.bucket.get( parentBlock ) ) {
					   CFGBlock y = this.AncestorWithLowestSemi1( v );
					   if( semi.get( y ) == semi.get( v ) ){
						   idom.put( v, parentBlock );
						   parentBlock.AddDomChild( v );
					   }
					   else this.samedom.put( v, y );
					}
					this.ClearBucket( parentBlock );
				}		
			}
			
			for( int i = 1; i <= N - 1; ++i ){
				CFGBlock n = this.vertex.get( i );
				if( samedom.containsKey( n ) ){
					CFGBlock parent = idom.get( samedom.get( n ) );
					idom.put( n, parent );
					parent.AddDomChild( n );
				}
			}
			return rootNode;
		}
	}
	public static class CFGBlock{
				
		private CFGBlock domParent = null;
		private ArrayList< CFGBlock > domChildren = new ArrayList< CFGBlock >();
		private ArrayList< CodeBlock > statements = new ArrayList< CodeBlock >();
		private ArrayList< CFGBlock > successors = new ArrayList< CFGBlock >();
		private ArrayList< CFGBlock > predecessors = new ArrayList< CFGBlock >();
		private HashMap< String, ArrayList< Integer > > varDefined = new HashMap< String, ArrayList< Integer > >();
		private HashMap< String,  CodeBlock  > phiFunctions = new HashMap< String, CodeBlock   > ();

		public boolean isDeleted = false;
		//Register Allocation
		private Integer fromLocation = 0;
		private Integer toLocation = 0;
		private Boolean isLoopStartingBlock = false;
		private Integer loopEndingLocation = -1;
		private CFGBlock loopStartingBlock = null;
		private HashMap<Integer, String> MapVirtualNoVsLabelValue = new HashMap<Integer, String>();
		private HashMap<String , Integer> MapLabelValueVsVirtualNo = new HashMap<String, Integer>();
		private ArrayList<String> liveIn = new ArrayList<String>();
		//private HashMap<CFGBlock, ArrayList<String>> phiInputsBlocks = new HashMap<CFGBlock, ArrayList<String>>();
		private HashMap<Integer, HashMap<String, ArrayList<String>>> moveInstFromRegAlloc = new HashMap<Integer, HashMap<String, ArrayList<String>>>();
		private HashMap<String, HashMap<Integer, String>> tempIdFix = new HashMap<String, HashMap<Integer,String>>();
		private HashMap<String, HashMap<Range, String>> mappingOfVirtualToActualRegister = 
			new HashMap<String, HashMap<Range,String>>();
				
		public void AddUncondBra( CFGBlock tonode ){
			CodeBlock cdBlk = CodeBlock.generateUnCondBranch();
			cdBlk.jumpLabel = new String( tonode.BlockLabel() );
			this.statements.add( cdBlk );
		}
		public void putTempIdFix(String moveData, Integer loc, String tempId) {
			if(tempIdFix.containsKey(moveData)){
				tempIdFix.get(moveData).put(loc, tempId);
			}else{
				HashMap<Integer, String> temp = new HashMap<Integer, String>();
				temp.put(loc, tempId);
				tempIdFix.put(moveData, temp);
			}
		}

		
		public HashMap<String, CodeBlock> getPhiFunctions() {
			return phiFunctions;
		}
		
		public void AddMappingOfVirtualToActualRegister(String virtualReg, HashMap<Range, String> mapping) {
			if(mapping != null && mapping.size()>0){
				if(mappingOfVirtualToActualRegister.containsKey(virtualReg)){
					for(Range eachRange: mapping.keySet()){
						mappingOfVirtualToActualRegister.get(virtualReg).put(eachRange, mapping.get(eachRange));
					}
				}else{
					mappingOfVirtualToActualRegister.put(virtualReg, mapping);
				}
			}
		}

		public void AddMoveInstFromRegAlloc(Integer loc, String moveFrom, String moveTo){
			if(moveInstFromRegAlloc.containsKey(loc)){
				if(!moveInstFromRegAlloc.get(loc).containsKey(moveFrom)){
					ArrayList<String> temp = new ArrayList<String>();
					temp.add(moveTo);
					moveInstFromRegAlloc.get(loc).put(moveFrom, temp);
				}else{
					moveInstFromRegAlloc.get(loc).get(moveFrom).add(moveTo);
				}
			}else{
				HashMap<String, ArrayList<String>> moveInfo = new HashMap<String, ArrayList<String>>();
				ArrayList<String> temp = new ArrayList<String>();
				temp.add(moveTo);
				moveInfo.put(moveFrom, temp);
				moveInstFromRegAlloc.put(loc, moveInfo);
			}
		}
		
		private String GetActualRegisterValue(String virtualReg, Integer position){
			String returnValue = null;
			
			HashMap<Range, String> tempValue = mappingOfVirtualToActualRegister.get(virtualReg);
			if(tempValue != null){
				for(Range eachRange: tempValue.keySet()){
					if(eachRange.IsCovered(position)){
						returnValue = tempValue.get(eachRange);
						break;
					}
				}
				
			}
			
			return returnValue;
		}
		
		private void AssignRegisterLocation(FrameInfo currentInfo, String codeBlockLabel){
			if(intermediateObjects.InterRep.globalSymTab.isGlobal(currentInfo.tempID)){
				currentInfo.setRegisterPosition(
						"G"+intermediateObjects.InterRep.globalSymTab.getGlobalRegisterSpillingLoc(
								currentInfo.tempID));
				return;
				
			}
			String temp = currentInfo.serializeMe();
			String registerValue = GetActualRegisterValue(temp, MapLabelValueVsVirtualNo.get(codeBlockLabel));
			currentInfo.setRegisterPosition(registerValue);
		}
		
		private void UpdateAllRegisterLocation(){
			for(CodeBlock eachCB: phiFunctions.values()){
				if(!eachCB.isDeleted){
					AssignRegisterLocation(eachCB.outputTemporary, eachCB.label);
					
					for(FrameInfo op: eachCB.operands){
						AssignRegisterLocation(op, eachCB.label);
					}
				}
			}
			for(CodeBlock eachCB: statements){
				if(!eachCB.isDeleted){
					if(eachCB.opCode == CodeBlock.kSUB){
						System.out.println();
					}
					if(!eachCB.isArgPassingStatement){
						AssignRegisterLocation(eachCB.outputTemporary, eachCB.label);
					}
					
					
					for(FrameInfo op: eachCB.operands){
						if(eachCB.opCode == CodeBlock.kMOVE && op.serializeMe().contains("RETURN")){
							continue;
						}
						AssignRegisterLocation(op, eachCB.label);
					}
				}
			}			
		}
		private Integer NumberofPhiStatement(){
			Integer returnValue =0;
			for(CodeBlock eachPhiStatement: phiFunctions.values()){
				if(!eachPhiStatement.isDeleted){
					returnValue++;
				}
			}
			return returnValue;
		}
		
		ArrayList<Integer> insertLocationArray = new ArrayList<Integer>();
		ArrayList<ArrayList<CodeBlock>> listOfCodeBlock = new ArrayList<ArrayList<CodeBlock>>();
		
		
		
		public void OrderAndInsertMoves(){
			UpdateAllRegisterLocation();
			ArrayList<String> tempList = new ArrayList<String>();
			insertLocationArray.clear();
			listOfCodeBlock.clear();
			for(Integer eachLocation:moveInstFromRegAlloc.keySet()){
				HashMap<String, ArrayList<String>> moveInstAtCurrentPosition = moveInstFromRegAlloc.get(eachLocation);
				HashMap<String, ArrayList<String>> tempofMoveInstAtCurrentPosition = (HashMap<String, ArrayList<String>>)moveInstAtCurrentPosition.clone();
				HashMap<String, Integer> moveFromToIteratorKey = new HashMap<String, Integer>();
				
				for(String eachMoveFrom: moveInstAtCurrentPosition.keySet()){
					moveFromToIteratorKey.put(eachMoveFrom, moveInstAtCurrentPosition.get(eachMoveFrom).size()-1);
				}
				
				Boolean isCurrentMoveInserted = false;
				Integer insertLocation = (eachLocation - fromLocation - (NumberofPhiStatement()*2))/2 ;
				ArrayList<CodeBlock> newMoveStatementInserted = new ArrayList<CodeBlock>();
				for(String eachMoveFrom: moveInstAtCurrentPosition.keySet()){
					isCurrentMoveInserted = false;
					tempList.clear();
					while(!isCurrentMoveInserted){
						
						if(moveFromToIteratorKey.get(eachMoveFrom) >=0){
							String eachMoveTo = moveInstAtCurrentPosition.get(
									eachMoveFrom).get(moveFromToIteratorKey.get(eachMoveFrom));
							if(tempList.contains(eachMoveTo)){
								//Insert Temp register
								newMoveStatementInserted.add(ConstructMoveStatementRegAlloc(eachLocation, eachMoveFrom,"temp"));
								
								//TODO:
								
							}else if(tempofMoveInstAtCurrentPosition.containsKey(eachMoveTo)){
								tempList.add(eachMoveFrom);
								eachMoveFrom = eachMoveTo;
								isCurrentMoveInserted = false;
								continue;
							}else{
								newMoveStatementInserted.add(ConstructMoveStatementRegAlloc(eachLocation, eachMoveFrom,eachMoveTo));
								tempofMoveInstAtCurrentPosition.remove(eachMoveFrom);
								moveFromToIteratorKey.put(eachMoveFrom, moveFromToIteratorKey.get(eachMoveFrom)-1);
							}					
						}else
						{
							if(tempList.isEmpty()){
								isCurrentMoveInserted = true;
								continue;
							}
							eachMoveFrom = tempList.remove(tempList.size() -1);
						}
					}
				}
				
				Integer statementSize = StatementListSize();
				if(insertLocation == (statementSize-1)){
					CodeBlock lastStatement = getStatementAtIndex(insertLocation);
					if(lastStatement.opCode > 10 && lastStatement.opCode <18){
						//DoNothing
					}else{
						insertLocation = statementSize;
					}
				}
				Boolean j = false ;
				
				for(int i=0;i<insertLocationArray.size();i++){
					if(insertLocationArray.get(i) == insertLocation){
						if(insertLocation ==6){
							j=true;
						}
						listOfCodeBlock.get(i).addAll(newMoveStatementInserted);
						j=true;
						break;
					}else if(insertLocationArray.get(i)> insertLocation){
						if(insertLocation ==6){
							j=true;
						}
						insertLocationArray.add(i, insertLocation);
						listOfCodeBlock.add(i, newMoveStatementInserted);
						j=true;
						break;
					} 
				}
				
				if(j == false){
					insertLocationArray.add(insertLocation);
					listOfCodeBlock.add(newMoveStatementInserted);
				}				
			}
			InsertAll();
		}
		
		public void InsertAll(){
			Integer adjustLoc = 0;
			
			for(int i = 0;i<insertLocationArray.size() ;i++){
				Integer statementSize = StatementListSize();
				Integer insertLocation = insertLocationArray.get(i);
				ArrayList<CodeBlock> newMoveStatementInserted = listOfCodeBlock.get(i);
				Integer tempLocation = insertLocation;
				Integer temp =0;
				for(CodeBlock newEachMoveStatement: newMoveStatementInserted){
					if((adjustLoc+insertLocation) == statementSize){
						statements.add(newEachMoveStatement);
						System.out.println("Added at last : Move " + newEachMoveStatement.operands.get(0).serializeMe()
								+ " "+  newEachMoveStatement.operands.get(1).serializeMe());
					}else{
						int x = adjustLoc+tempLocation;
						System.out.println("Added at "+ x +" : Move " + newEachMoveStatement.operands.get(0).serializeMe()
								+ " "+  newEachMoveStatement.operands.get(1).serializeMe());
						AddToStatementList(adjustLoc + tempLocation, newEachMoveStatement);
						temp ++;
						tempLocation++;
					}
				}
				adjustLoc +=temp;
			}
		}
		
		public void DeleteAllPhiBlock(){
			//Delete all phi Blocks
			for(String eachPhiFunction: phiFunctions.keySet()){
				CodeBlock phiCodeBlock = phiFunctions.get(eachPhiFunction);
				phiCodeBlock.isDeleted = true;
			}
		}
		
		private CodeBlock ConstructMoveStatementRegAlloc(Integer loc, String fromMove, String toMove){
			FrameInfo fromFrameInfo = null;
			try{
				fromFrameInfo = intermediateObjects.InterRep.globalSymTab.generateConstantFrameInfo(Integer.parseInt(fromMove));
			}catch(NumberFormatException  nfe){
				String fromTemp = tempIdFix.get(fromMove).get(loc+2);
				if(fromTemp == null){
					fromTemp = tempIdFix.get(fromMove).get(loc);
					if(fromTemp == null){
						fromTemp = tempIdFix.get(fromMove).get(loc-2);
					}
				}
				fromFrameInfo = intermediateObjects.InterRep.globalSymTab.generateNewFrameInfo(fromTemp);
				fromFrameInfo.registerPosition = fromMove;
			}
			String toTemp = tempIdFix.get(toMove).get(loc+2);
			if(toTemp == null){
				toTemp = tempIdFix.get(toMove).get(loc);
				if(toTemp == null){
					toTemp = tempIdFix.get(toMove).get(loc-2);
				}
			}
			FrameInfo toFrameInfo = intermediateObjects.InterRep.globalSymTab.generateNewFrameInfo(toTemp);
			toFrameInfo.registerPosition = toMove;
			return CodeBlock.generateMoveOrStoreOP(fromFrameInfo, toFrameInfo, CodeBlock.kMOVE);
		}
		
		private void AddToStatementList(Integer index, CodeBlock cb){
			Integer temp = 0;
			Integer statementIndex = 0;
			for(CodeBlock eachStatements: statements){
				if(!eachStatements.isDeleted){
					if(temp == index){
						statements.add(statementIndex, cb);
						break;
					}
					temp++;
				}
				statementIndex++;
			}
			if( 0 == index ){
				String blkLabel = this.BlockLabel();
				for( CFGBlock pred : this.predecessors ){
					pred.ReplaceJumpLabelTo( blkLabel );
				}
			}
		}
		
		private Integer StatementListSize(){
			Integer returnValue =0;
			for(CodeBlock eachStatements: statements){
				if(!eachStatements.isDeleted){
					returnValue++;
				}
			}
			return returnValue;
		}
		
		private CodeBlock getStatementAtIndex(Integer index){
			CodeBlock returnValue = null;
			Integer temp = 0;
			
			for(CodeBlock eachStatements: statements){
				if(!eachStatements.isDeleted){
					if(temp == index){
						returnValue = eachStatements;
						break;
					}
					temp++;
				}
			}
			
			return returnValue;
		}		
		
		public Integer getSizeOfPhiAndStatement(){
			Integer returnValue = 0;
			for(CodeBlock eachCB : phiFunctions.values()){
				if(!eachCB.isDeleted){
					returnValue ++;
				}
			}
			for(CodeBlock eachCB: statements){
				if(!eachCB.isDeleted){
					returnValue ++;
				}
			}
			
			return returnValue;
		}
		
		public Integer GetVirtualNumberForLabelValue(String labelValue){
			Integer returnValue = -1;
			if(MapLabelValueVsVirtualNo.containsKey(labelValue)){
				returnValue = MapLabelValueVsVirtualNo.get(labelValue);
			}
			return returnValue;
		}
		
		public Boolean getIsLoopStartingBlock() {
			return isLoopStartingBlock;
		}

		public void setIsLoopStartingBlock(Boolean isLoopStartingBlock) {
			this.isLoopStartingBlock = isLoopStartingBlock;
		}

		public Integer getLoopEndingLocation() {
			return loopEndingLocation;
		}

		public void setLoopEndingLocation(Integer loopEndingLocation) {
			this.loopEndingLocation = loopEndingLocation;
		}

		public CFGBlock getLoopStartingBlock() {
			return loopStartingBlock;
		}

		public void setLoopStartingBlock(CFGBlock loopStartingBlock) {
			this.loopStartingBlock = loopStartingBlock;
		}
			
		public HashMap<Integer, String> getMapVirtualNoVsLabelValue() {
			return MapVirtualNoVsLabelValue;
		}

		public ArrayList<String> getLiveIn() {
			return liveIn;
		}

		public void setLiveIn(ArrayList<String> liveIn) {
			this.liveIn = liveIn;
		}

		public void setMapVirtualNoVsLabelValue(Integer virtualNo, String labelValue) {
			MapVirtualNoVsLabelValue.put(virtualNo, labelValue);
		}

		public Integer getFromLocation() {
			return fromLocation;
		}

		public void setFromLocation(Integer fromLocation) {
			this.fromLocation = fromLocation;
		}

		public Integer getToLocation() {
			return toLocation;
		}

		public void setToLocation(Integer toLocation) {
			this.toLocation = toLocation;
		}

		public HashMap< String, CodeBlock > returnPhiFunctions(){
			return phiFunctions;
		}
		
		public ArrayList<FrameInfo> PhiInputOfCFGBlock(CFGBlock block){
			ArrayList<FrameInfo> returnValue = new ArrayList<FrameInfo>();
			
			int j = this.jthPredecessor( block );
			if( -1 == j ) 
				return returnValue;
			
			for(String phivalue: phiFunctions.keySet()){
				CodeBlock phidata = phiFunctions.get(phivalue);
				FrameInfo tempInfo = phidata.operands.get(j);
				if(tempInfo instanceof LocationInfo && 
						!intermediateObjects.InterRep.globalSymTab.isGlobal(tempInfo.tempID)){
					returnValue.add(tempInfo);
				}
			}					
			return returnValue;
		}
		
		public Integer GetLastPhiFunctionNumber(){
			if(NumberofPhiStatement() ==0){
				return 0;
			}
			return (fromLocation + 2* (NumberofPhiStatement()-1));
		}
		public FrameInfo getPhiFnOutputFrame(String var, CFGBlock predecessor){
			FrameInfo returnValue = null;
			
			int j = this.jthPredecessor( predecessor );
			if( -1 == j ) 
				return returnValue;
			
			CodeBlock varBlock = phiFunctions.get(var);
			returnValue = varBlock.outputTemporary;
			return returnValue;
		}
		
		public FrameInfo getPhiFnDefiningVarAndInputOfPred(String var, CFGBlock predecessor){
			FrameInfo returnValue = null;
			
			int j = this.jthPredecessor( predecessor );
			if( -1 == j ) 
				return returnValue;
			
			CodeBlock varBlock = phiFunctions.get(var);
			returnValue = varBlock.operands.get(j);
			return returnValue;
		}
		
		public void AddMapping(){
			int tempValue = fromLocation;
			for(CodeBlock eachCB : phiFunctions.values()){
				if(!eachCB.isDeleted){
					System.out.println(tempValue +";" +eachCB.label);
					MapVirtualNoVsLabelValue.put(tempValue, eachCB.label);
					MapLabelValueVsVirtualNo.put(eachCB.label, tempValue);
					tempValue = tempValue +2;
				}
			}
			for(CodeBlock eachCB: statements){
				if(!eachCB.isDeleted){
					System.out.println(tempValue +";" +eachCB.label);
					MapVirtualNoVsLabelValue.put(tempValue, eachCB.label);
					MapLabelValueVsVirtualNo.put(eachCB.label, tempValue);
					tempValue = tempValue +2;
				}
			}
		}
		
		
		public void AddDeclVariables( String fnName ){
			intermediateObjects.InterRep.VarDecl theVarDecl = intermediateObjects.InterRep.globalSymTab.getVarDeclInfo( fnName );
			if( null == theVarDecl ) return;
			
			ArrayList< String > theIdents = theVarDecl.getMIdentList();
			for( String s : theIdents ){
				try{
					this.InsertIntoDefList( intermediateObjects.InterRep.globalSymTab.getAddressInfo( s ) );
				}
				catch( Exception e ){
					//TODO
				}
			}
		}
	
		public int jthPredecessor( CFGBlock pred ){
			int j = -1;
			if( predecessors.contains( pred ) )
				return predecessors.indexOf( pred );
			return j;
		}
		public void SetDomParent( CFGBlock parent ){
			domParent = parent;
			parent.domChildren.add( this );
		}
		
		public ArrayList< CodeBlock > GetStatementsList(){
			return statements;
		}
		public boolean HasPhiFunction( String var ){
			return phiFunctions.containsKey( var );
		}
		
		public CodeBlock AddPhiFunction( String var ) {
			if( this.phiFunctions.containsKey( var ) )
				return this.phiFunctions.get( var );
			try{
				CodeBlock cd = CodeBlock.generatePhiBlock( var, this.predecessors.size() );
				this.phiFunctions.put( var, cd );
				return cd;
			}
			catch( Exception e ){
				//TODO
			}
			return null;
			
		}
		
		public String MakeOutputTempUnique( String var ){
			if( !this.phiFunctions.containsKey( var ) )return null;
			CodeBlock cd = this.phiFunctions.get( var );
			cd.outputTemporary = intermediateObjects.InterRep.globalSymTab.generateNewFrameInfo( cd.label );
			this.phiFunctions.remove( var );
			this.phiFunctions.put( cd.label, cd );
			return cd.label;
		}
		public CodeBlock RenameJthPhiOperand( String var, CFGBlock pred, FrameInfo fm ){
			int j = this.jthPredecessor( pred );
			if( -1 == j ) return null;
			
			CodeBlock phiBlock = this.phiFunctions.get( var );
			phiBlock.operands.set( j , fm.Clone() );
			this.phiFunctions.put( var, phiBlock );
			return phiBlock;
		}
		
		public boolean RemoveJthPhiOperand( String var, CFGBlock pred, HashMap< String, FrameInfo > replacements ){
			int j = this.jthPredecessor( pred );
			if( -1 == j ) return false;
			CodeBlock phiBlock = this.phiFunctions.get( var );
			phiBlock.operands.remove( j );
			FrameInfo fmTemp = null;
			if( phiBlock.operands.size() == 1 ){
				String lhsName = phiBlock.returnLVALOperand();
				FrameInfo fm = phiBlock.returnMovOperand();
				replacements.put( lhsName, fm );
				phiBlock.isDeleted = true;
				return true;
			}
			/*else if( ( fmTemp = phiBlock.PhiAllButOneSame() ) != null ){
				String lhsName = phiBlock.returnLVALOperand();
				replacements.put( lhsName, fmTemp );
				phiBlock.isDeleted = true;
				return true;
			}*/
			return false;
		}
		public void RemovePhiBlock( String var ){
			this.phiFunctions.remove( var );
		}
		
		public CFGBlock GetDomParent() {
			return domParent;
		}
		
		public ArrayList< CFGBlock > GetDomChildren(){
			return domChildren;
		}
		public void SetDomChildren( ArrayList< CFGBlock > theChildren ){
			domChildren = theChildren;
			for( int i = 0; i < theChildren.size(); ++i ){
				CFGBlock theChild = theChildren.get( i );
				theChild.domParent = this;
			}
		}
		
		public Set< String > returnVars(){
			return this.varDefined.keySet();
		}
		
		public boolean isVarDefined( String var ){
			return this.varDefined.containsKey( var );
		}
		public void DefineVar( String var ){
			if( this.phiFunctions.containsKey( var ) ){
				CodeBlock cd = this.phiFunctions.get( var );
				this.InsertPhiIntoDefList( cd.outputTemporary );
			}
		}
		private int CompareTwoStrings( String s1, String s2 ){
			return s1.compareTo( s2 );
		}
		public void AddDomChild( CFGBlock theChild ){
			int sz = domChildren.size();
			for( int i = 0; i < sz; ++i ){
				if( CompareTwoStrings( theChild.BlockLabel(), domChildren.get( i ).BlockLabel() ) >= 0 ){
					continue;
				}
				else{
					domChildren.add( i, theChild );
					theChild.domParent = this;
					return;
				}
			}
			domChildren.add( theChild );
			theChild.domParent = this;
		}
		public CFGBlock(){
			super();
		}
		
		public void printMe(){
			System.out.println("Start of a new block");
			for( int i = 0; i < statements.size(); ++i ){
				CodeBlock curStmt = statements.get( i );
				String s = CodeBlock.serializeMe( curStmt );
				System.out.print( s  );
			}
		}
		public String JumpLabel(){
			if( 0 == statements.size() ) return null;
			intermediateObjects.InterRep.CodeBlock cdBlk = statements.get( statements.size() - 1 );
			if( cdBlk.isDeleted || !( cdBlk.opCode >= 11 && cdBlk.opCode <= 17 ) ) return null;
			return cdBlk.jumpLabel;
		}
		public void ReplaceSuccessor( CFGBlock orig, CFGBlock newSucc ){
			int indx = successors.indexOf( orig );
			if( -1 == indx )return;
			if( null == newSucc ){
				successors.remove( indx );
				return;
			}
			
			successors.set( indx, newSucc );
			if( orig.BlockLabel().equals( this.JumpLabel() ) ){
				this.ReplaceJumpLabelTo( newSucc.BlockLabel() );
			}
			
			
		}
		
		public void FixupPredLabel(){
			String label = null;
			for( intermediateObjects.InterRep.CodeBlock cd : statements ){
				if( cd.isDeleted ) continue;
				label = cd.label;
				break;
			}
			for( CFGBlock pred : predecessors ){
				pred.ReplaceJumpLabelTo( label );
			}
		}
		public void DeleteNode(){
			isDeleted = true;
			//set the graph straight.
			//any deleted node can have only 1 successor
			CFGBlock succ = null;
			if( this.successors.size() > 0 ){
				succ = successors.get( 0 );
				int indx = succ.predecessors.indexOf( this );
				if( -1 != indx ){
					succ.predecessors.addAll( indx, this.predecessors );
					indx = succ.predecessors.indexOf( this );
					if( indx != -1 ){
						succ.predecessors.remove( indx );
					}
				}
			//	succ.predecessors = this.predecessors;
			}
			for( CFGBlock pred : predecessors ){
				pred.ReplaceSuccessor( this, succ );
			}
			if( domParent != null ){
				this.domParent.SetDomChildren( domChildren );
			}
		}
		/*private boolean DeleteEdgePrivate( CFGBlock pred, HashMap< String, intermediateObjects.InterRep.FrameInfo > replacements ){
			int indx = this.jthPredecessor( pred );
			if( -1 == indx ) return false;
			
			predecessors.remove( indx );
			Set< String > phiNames = this.phiFunctions.keySet();
			boolean didInsert = false;
			for( String var : phiNames ){
				boolean temp = this.RemoveJthPhiOperand( var, pred, replacements );
				didInsert = didInsert || temp;
			}
			if( 0 == predecessors.size() ){
				this.isDeleted = true;
				for( CFGBlock succ : successors ){
					boolean temp = succ.DeleteEdge( this , replacements );
					didInsert = didInsert || temp;
				}
			}
		}*/
		public boolean DeleteEdge( CFGBlock pred, HashMap< String, intermediateObjects.InterRep.FrameInfo > replacements, Queue< CFGBlock > nodeQueue ){
			/*int indx = this.jthPredecessor( pred );
			if( -1 == indx ) return false;
			
			predecessors.remove( indx );
			pred.ReplaceSuccessor( this, null );
			Set< String > phiNames = this.phiFunctions.keySet();
			boolean didInsert = false;
			for( String var : phiNames ){
				boolean temp = this.RemoveJthPhiOperand( var, pred, replacements );
				didInsert = didInsert || temp;
			}
			if( 0 == predecessors.size() ){
				this.isDeleted = true;
				for( CFGBlock succ : successors ){
					//CFGBlock succ = successors.get( i );
					boolean temp = succ.DeleteEdge( this, replacements );
					didInsert = didInsert || temp;
				}
			}
			
			return didInsert;*/
			
			HashMap< CFGBlock, ArrayList< CFGBlock > > hack = new HashMap< CFGBlock, ArrayList< CFGBlock > >();
			boolean didInsert = DeleteEdgePrivate( pred, replacements, hack, nodeQueue );
			Set< CFGBlock > hackKey = hack.keySet();
			for( CFGBlock key : hackKey ){
				ArrayList< CFGBlock > valSet = hack.get( key );
				for( CFGBlock val : valSet ){
					key.ReplaceSuccessor( val, null );
				}
			}
			return didInsert;
		}
		
		private boolean IsSelfLoop(  ){
			if( 0 == predecessors.size() || 1 < predecessors.size() ) return false; 
			
			CFGBlock pred = predecessors.get( 0 );
			if( pred.predecessors.size() == 0 || 1 < pred.predecessors.size() ) return false;
			CFGBlock predPred = pred.predecessors.get( 0 );
			if( predPred.BlockLabel().equals( BlockLabel() ) )return true;
			return false;
		}
		private boolean DeleteEdgePrivate( CFGBlock pred, HashMap< String, intermediateObjects.InterRep.FrameInfo > replacements, HashMap< CFGBlock, ArrayList< CFGBlock > > skankyHack, Queue< CFGBlock > nodeQueue ){
			int indx = this.jthPredecessor( pred );
			if( -1 == indx ) return false;
			
			//pred.ReplaceSuccessor( this, null );
			if( skankyHack.get( pred ) != null ){
				skankyHack.get( pred ).add( this );
			}
			else{
				ArrayList< CFGBlock > list = new ArrayList< CFGBlock >();
				list.add( this );
				skankyHack.put( pred, list );
			}
			Set< String > phiNames = this.phiFunctions.keySet();
			boolean didInsert = false;
			for( String var : phiNames ){
				boolean temp = this.RemoveJthPhiOperand( var, pred, replacements );
				didInsert = didInsert || temp;
			}
			predecessors.remove( indx );
			if( this.BlockLabel().equals("foo:51")){
				boolean a = true;
			}
			if( IsSelfLoop() ){
				CFGBlock newPred = predecessors.remove( 0 );
				if( skankyHack.get( newPred ) != null ){
					skankyHack.get( newPred ).add( this );
				}
				else{
					ArrayList< CFGBlock > list = new ArrayList< CFGBlock >();
					list.add( this );
					skankyHack.put( newPred, list );
				}
			}
			if( 0 == predecessors.size() ){
				predecessors.clear();
				this.isDeleted = true;
				for( CFGBlock succ : successors ){
					//CFGBlock succ = successors.get( i );
					boolean temp = succ.DeleteEdgePrivate( this, replacements, skankyHack, nodeQueue );
					didInsert = didInsert || temp;
				}
			}
			else if( didInsert ){
				nodeQueue.add( this );
			}
			return didInsert;
		}
		public boolean IsEmpty(){
			boolean validSt = false;
			for( intermediateObjects.InterRep.CodeBlock cd : statements ){
				if( !cd.isDeleted ){
					validSt = true;
					break;
				}
			}
			return !validSt && this.phiFunctions.isEmpty();
		}
		
		public void AddSuccessor( CFGBlock succ ){
			this.successors.add( succ );
			succ.predecessors.add( this );
		}
		
		private void InsertIntoDefList( FrameInfo var ){
			String varname = intermediateObjects.InterRep.globalSymTab.variableName(var);
			if( this.varDefined.containsKey( varname ) ){
				this.varDefined.get( varname ).add( statements.size() - 1 );
				return;
			}
			ArrayList< Integer > temp = new ArrayList< Integer >();
			temp.add( statements.size() - 1 );
			this.varDefined.put( varname, temp );
		}
		
		private void InsertPhiIntoDefList( FrameInfo var ) {
			if( this.varDefined.containsKey( var ) ) return;
			String varname = intermediateObjects.InterRep.globalSymTab.variableName(var);
			ArrayList< Integer > temp = new ArrayList< Integer >();
			temp.add( -1 );
			this.varDefined.put( varname, temp );
		}
		public void AddStatement( CodeBlock cdBlk ){
			cdBlk = cdBlk.Clone();
			cdBlk.ProcessOperandsForMain();
			statements.add(cdBlk );
			if( cdBlk.isLetMoveStatement ){
				InsertIntoDefList( cdBlk.outputTemporary );
			}
			
		}
		
		public void AddPredecessor( CFGBlock pred ){
			pred.AddSuccessor( this );
		}
		
		public void AddPredecessors( ArrayList< CFGBlock > predList ){
			for( int i = 0; i < predList.size(); ++i  ){
				this.AddPredecessor( predList.get( i ) );
			}
		}
		
		public void AddSuccessors( ArrayList< CFGBlock > succList ){
			for( int i = 0; i < succList.size(); ++i ){
				this.AddSuccessor( succList.get( i ) );
			}
		}
		
		public String BlockLabel() {
			if( statements.size() == 0 ){
				return "ROOT";
			}
			return statements.get( 0 ).label;
		}
		
		
		public boolean IsJumpLabel( String label ){
			return BlockLabel().equals( label );
		}
		
		public void ReplaceJumpLabelTo( String to ){
			if( 0 == statements.size() ) return;
			intermediateObjects.InterRep.CodeBlock cdBlk = statements.get( statements.size() - 1 );
			if( cdBlk.isDeleted || !( cdBlk.opCode >= 11 && cdBlk.opCode <= 17 ) ) return;
			if( to.equals( "bar:12") && BlockLabel().equals("bar:5")){
				boolean a = true;
			}
			cdBlk.jumpLabel = new String( to );
		}
		
		public ArrayList< CFGBlock > SuccessorList() {
			return successors;
		}
		
		public ArrayList< CFGBlock > PredecessorList(){
			return predecessors;
		}
		
		//phi blocks will be added to first codeblock of this cfgblock thru interfaces exposed by codeBlock.
	}
	
	private static class Helper{
		//private
		private HashMap< String, CFGBlock > resolvedJumpLabels = new HashMap< String, CFGBlock >();
		private HashMap< String, ArrayList< CFGBlock > > unresolvedJumpLabels = new HashMap< String, ArrayList< CFGBlock> >();
		private ArrayList< String > funcWhileLabels = null;
		public Helper( String funcName ){
			funcWhileLabels = intermediateObjects.InterRep.globalSymTab.getWhileLabels( funcName );
		}
		public CFGBlock resolvedJumpTarget( String jumpLabel, CFGBlock current ){
			if( resolvedJumpLabels.containsKey( jumpLabel ) ){
				CFGBlock theBlk = resolvedJumpLabels.get( jumpLabel );
				theBlk.AddPredecessor( current );
				return theBlk;
			}
			return null;
		}
		
		public boolean unresolvedJumpTarget( String jumpLabel ){
			if( unresolvedJumpLabels.containsKey( jumpLabel ) )
				return true;
			return false;
		}
		
		public void resolveJumpTarget( String jumpLabel, CFGBlock node ){
			if( unresolvedJumpLabels.containsKey( jumpLabel ) ){
				ArrayList< CFGBlock > predecessors = unresolvedJumpLabels.get( jumpLabel );
				node.AddPredecessors( predecessors );
				unresolvedJumpLabels.remove( jumpLabel );
			}
			resolvedJumpLabels.put( jumpLabel, node );
		}
		
		public void addUnResolvedJumpTarget( String jumpLabel, CFGBlock newNode ){
			if( unresolvedJumpLabels.containsKey( jumpLabel ) ){
				ArrayList< CFGBlock > theBlock = unresolvedJumpLabels.get( jumpLabel );
				theBlock.add( newNode );
				return; //pass by reference baby \m/
			}
			ArrayList< CFGBlock > theTemp = new ArrayList< CFGBlock >();
			theTemp.add( newNode );
			unresolvedJumpLabels.put( jumpLabel, theTemp );
			
		}
		public void ParsingError() throws Exception{
			// a bit hacky but this shud be invoked last.
			if( unresolvedJumpLabels.isEmpty() == false )
				throw new Exception( "Some unresolved basic block targets are still present in the current frame " );
		}
		
		private CFGBlock createNewCFGBlock( CodeBlock firstStatement ){
			CFGBlock newBlk = new CFGBlock();
			newBlk.AddStatement( firstStatement );
			return newBlk;
		}
		
		public CFGBlock EnsureBlockPresent( CFGBlock theBlock, CFGBlock prevBlock, CodeBlock statement ){
			if( null != theBlock ){
				if( !this.unresolvedJumpTarget( statement.label ) && !this.funcWhileLabels.contains( statement.label ) ){
					theBlock.AddStatement( statement );
					return theBlock;
				}
				prevBlock = theBlock;
				theBlock = null;
			}
			theBlock =  createNewCFGBlock( statement );
			if( null != prevBlock ) prevBlock.AddSuccessor( theBlock );
			resolveJumpTarget( statement.label, theBlock );
			return theBlock;
		}
		
		public boolean isUnCondBranch( CodeBlock statement ){
			return statement.opCode == CodeBlock.kBRA && ( !statement.isCall && !statement.isDeleted );
		}
		
		public boolean isCondBranch( CodeBlock statement ){
			return (CodeBlock.kBNE <= statement.opCode && statement.opCode <= CodeBlock.kBGT ) && !statement.isDeleted;
		}
	}
	public static CFGBlock BuildCFGBlock( String funcName, ArrayList< CodeBlock> statements ) throws Exception{
		Helper helper = new Helper( funcName ); //this ensures all memory used in helper is reclaimed.
		CFGBlock currentBlock = null;
		CFGBlock lastBlock = null;
		CFGBlock rootNode = new CFGBlock();
		lastBlock = rootNode;
		int sz = statements.size();
		for( int i = 0; i < sz; ++i ){
			CodeBlock curStmt = statements.get( i );
			boolean isCondBranch = helper.isCondBranch( curStmt );
			boolean isUncondBranch = helper.isUnCondBranch( curStmt );
			currentBlock = helper.EnsureBlockPresent( currentBlock, lastBlock, curStmt );
			if( isCondBranch || isUncondBranch ){
				CFGBlock succ = helper.resolvedJumpTarget( curStmt.jumpLabel, currentBlock );
				if( null == succ ){
					helper.addUnResolvedJumpTarget( curStmt.jumpLabel, currentBlock );
				}
				if( isUncondBranch ) lastBlock = null;
				else lastBlock = currentBlock;
				
				currentBlock = null;
			}
		}
		if( null!= rootNode ){
			rootNode.AddDeclVariables( funcName );
		}
		return rootNode;
	}
} 

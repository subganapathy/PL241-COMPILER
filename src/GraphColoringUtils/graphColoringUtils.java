package GraphColoringUtils;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Comparator;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.Collections;

import cfg.cfg.CFGBlock;
import intermediateObjects.InterRep.CodeBlock;
import intermediateObjects.InterRep.FrameInfo;
import intermediateObjects.InterRep.ConstFrameInfo;
import intermediateObjects.InterRep;

/**
 * Top level namespace class in which various helper sub classes are defined.
 * @author sganapat
 *
 */
public class graphColoringUtils {
	public static final int NREGS = 32; //will be updated later!
	public static final int ARGSTARTREGISTER = 10;
	public static final int RETURNREGISTER = 15;
	public static final int RETURNVALUEREGISTER = 16;
	public static final int GLOBALPOINTER = 30;
	public static final int STACKPOINTER = 29;
	public static final int FRAMEPOINTER = 28;
	public static final int ZERO = 0;
	
	public static List<WebRecord> symbolicRegisters = new ArrayList<WebRecord> ();
	
	/**
	 * Used by register coalescing to merge the destination of a coalescable move with the source and delete the source
	 * from the symbolic registers list!
	 * @param to
	 * @param from
	 * @return
	 */
	public static Pair<String, Integer> mergeAndRemoveFromSymbolicRegisters (final WebRecord to, final WebRecord from) {
		to.merge(from);
		int indx = symbolicRegisters.indexOf(from);
		if (-1 == indx) {
			throw new Error ("The from web record is not found in the array, error!");
		}
		final WebRecord rightMost = symbolicRegisters.get(symbolicRegisters.size() - 1);
		symbolicRegisters.set(indx, rightMost);
		symbolicRegisters.remove(symbolicRegisters.size() - 1);
		return new Pair<String, Integer> (rightMost.getSymbolicRegister(), indx);
	}
	
	public static String intToReg( int regnum) {
		return ((regnum >= NREGS) ? "s" + regnum : "r" + regnum);
	}

	/**
	 * 
	 * POJO for std::pair<T,U> #Copied
	 * @author sganapat
	 *
	 * @param <T>
	 * @param <U>
	 */

public static class Pair <T, U>
{
   private final T first;
   private final U second;
   private transient final int hash;

   public Pair( T f, U s )
   {
    this.first = f;
    this.second = s;
    hash = (first == null? 0 : first.hashCode() * 31)
          +(second == null? 0 : second.hashCode());
   }

   public T getFirst()
   {
    return first;
   }
   public U getSecond()
   {
    return second;
   }

   @Override
   public int hashCode()
   {
    return hash;
   }

   @Override
   public boolean equals( Object oth )
   {
    if ( this == oth )
    {
      return true;
    }
    if ( oth == null || !(getClass().isInstance( oth )) )
    {
      return false;
    }
    @SuppressWarnings("unchecked")
    Pair<T, U> other = (Pair<T, U>)getClass().cast(oth);
    return (first == null? other.first == null : first.equals( other.first ))
     && (second == null? other.second == null : second.equals( other.second ));
   }
   
   @Override
   public String toString () {
	   return "( " + first.toString() + ", " + second.toString() + " ) ";
   }
}

/**
 * A tuple of dfs ordered block number and instruction number.
 * along with some convenience functions. 
 * @author sganapat
 *
 */
public static class SymbolLocationInfo {
	private Pair<Integer, Integer> blockNumInsNumPair = null;
	public SymbolLocationInfo(final int blockNum, final int insNum) {
		blockNumInsNumPair = new Pair<Integer, Integer>(blockNum, insNum);
	}
	
	public int returnBlockNum() {
		return blockNumInsNumPair.getFirst();
	}
	
	public int returnInsNum() {
		return blockNumInsNumPair.getSecond();
	}
	
	public Pair<Integer, Integer> returnLocationInfo() {
		return blockNumInsNumPair;
	}
	
	@Override
	public int hashCode() {
		return blockNumInsNumPair.hashCode();
	}

    @Override
    public boolean equals( Object oth ) {
	    if ( this == oth )
	    {
	      return true;
	    }
	    if ( oth == null || !(getClass().isInstance( oth )) )
	    {
	      return false;
	    }
	    @SuppressWarnings("unchecked")
	    SymbolLocationInfo other = (SymbolLocationInfo)getClass().cast(oth);
	    return (blockNumInsNumPair == null? other.blockNumInsNumPair == null : blockNumInsNumPair.equals( other.blockNumInsNumPair ));
   }
    
    @Override
    public String toString () {
    	return "( " + blockNumInsNumPair.getFirst().toString() + ", " + blockNumInsNumPair.getSecond().toString() + " ) "; 
    }
}

/**
 * POJO for building a def use chain with each
 * definition represented as Pair<String, SymbolLocationInfo>
 * where String represents the canonical (non SSA) name and SymbolLocationInfo as above.
 * each use is a SymbolLocationInfo.
 * @author sganapat
 *
 */
public static class DefUseChain {
	private Map<Pair<String, SymbolLocationInfo>, ArrayList<SymbolLocationInfo>>  duChain =
		new HashMap<Pair<String, SymbolLocationInfo>, ArrayList<SymbolLocationInfo>> ();
	
	private Map<String, SymbolLocationInfo> defSite = new HashMap<String, SymbolLocationInfo>();
	private Map<String, ArrayList<SymbolLocationInfo>> unresolvedUses =
		new HashMap<String, ArrayList<SymbolLocationInfo>> ();
	
	private Map<String, String> ssaNameSymbolMap =
		new HashMap<String, String> ();

	public DefUseChain() {
		super();
	}
	
	private void insertIntoDuChain(final FrameInfo fm, int blocknum, int insnum) {
		if (fm instanceof ConstFrameInfo) {
			return;
		}
		final String symbol = fm.tempID;
		final String ssaName = ((fm.ssaName != null)? fm.ssaName : fm.tempID);
		final SymbolLocationInfo theSym = defSite.get(ssaName);
		if (!ssaNameSymbolMap.containsKey(ssaName)) {
			ssaNameSymbolMap.put(ssaName, symbol);
		}
		if (null == theSym) {
			if (!unresolvedUses.containsKey(ssaName)) {
				unresolvedUses.put(ssaName, new ArrayList<SymbolLocationInfo> ());
			}
			unresolvedUses.get(ssaName).add(new SymbolLocationInfo(blocknum, insnum));
			return;
		}
		final Pair<String, SymbolLocationInfo> key = new Pair<String, SymbolLocationInfo>
													(symbol, theSym);
		if (!duChain.containsKey(key)) {
			duChain.put(key, new ArrayList<SymbolLocationInfo> ());
		}
		duChain.get(key).add(new SymbolLocationInfo(blocknum, insnum));
	}
	
	private void markDefLoc(final FrameInfo fm, int blocknum, int insnum) {
		final String symbol = fm.tempID;
		final String ssaName = ((fm.ssaName != null)? fm.ssaName : fm.tempID);
		defSite.put(ssaName, new SymbolLocationInfo(blocknum, insnum));
		if (!ssaNameSymbolMap.containsKey(ssaName)) {
			ssaNameSymbolMap.put(ssaName, symbol);
		}
		final List<SymbolLocationInfo> unresolvedUseList = unresolvedUses.get(ssaName);
		final Pair<String, SymbolLocationInfo> key = new Pair<String, SymbolLocationInfo>
											(symbol, new SymbolLocationInfo(blocknum, insnum));
		if (!duChain.containsKey(key)) {
			duChain.put(key, new ArrayList<SymbolLocationInfo>());
		}
		if (unresolvedUses.containsKey(ssaName)) {
			duChain.get(key).addAll(unresolvedUseList);
			unresolvedUses.remove(ssaName);
		}
	}
	private void processInstruction (final CodeBlock stmt, int blocknum, int insnum) {
		if (stmt.isDeleted) return;
		for (final FrameInfo fmInfo : stmt.operands) {
			insertIntoDuChain(fmInfo, blocknum, insnum);
			if (stmt.opCode == CodeBlock.kMOVE) {
				break;
			}
		}
		if (stmt.isArgPassingStatement) return;
		final FrameInfo fmInfo = stmt.outputTemporary;
		if (null != fmInfo) {
			markDefLoc(fmInfo, blocknum, insnum);			
		}
	}
	
	private void resolveAllUnresolvedUses () {
		if (!unresolvedUses.isEmpty()) {
			for (final Map.Entry<String, ArrayList<SymbolLocationInfo>> entry : unresolvedUses.entrySet()) {
				final String ssaName = entry.getKey();
				final ArrayList<SymbolLocationInfo> useList = entry.getValue();
				final String key = ((ssaNameSymbolMap.containsKey(ssaName))? ssaNameSymbolMap.get(ssaName) : ssaName);
				final Pair<String, SymbolLocationInfo> duChainKey =
					new Pair<String, SymbolLocationInfo> (key, new SymbolLocationInfo (0, -1)); //this means the value of the variable has been defined 
				//in the prolog block.
				this.duChain.put(duChainKey, useList);
			}
		}
	}
	/**
	 * vertexList is the dfs order array of vertices.
	 * @param vertexList
	 * @return
	 */
	public Map<Pair<String, SymbolLocationInfo>, ArrayList<SymbolLocationInfo>>
		buildDefUseChain(final List<CFGBlock> vertexList) {
		for (int i = 0; i < vertexList.size(); ++i) {
			final CFGBlock cfgBlock = vertexList.get(i);
			final List<CodeBlock> statementList = cfgBlock.GetStatementsList();
			int j  = -1;
			for (final Map.Entry<String, CodeBlock> mapEntry : cfgBlock.getPhiFunctions().entrySet()) {
				++j;
				final CodeBlock cdBlock = mapEntry.getValue();
				processInstruction(cdBlock, i, j);			
			}
			for (final CodeBlock cdBlock : statementList) {
				j++;
				processInstruction(cdBlock, i, j);
			}
		}
		resolveAllUnresolvedUses ();
		return duChain;
	}
}

/**
 * POJO encapsulating a web and associating a symbolic register/real register 
 * as well as the symbol, along with its locations of defs and uses represented as symbolLocationInfos.
 * @author sganapat
 *
 */
public static class WebRecord {
	private String symbol = null;
	private final List<SymbolLocationInfo> defs = new ArrayList<SymbolLocationInfo>();
	private final List<SymbolLocationInfo> uses = new ArrayList<SymbolLocationInfo>();
	private boolean spill = false;
	private String symbolicRegister = null;
	private int stackDisplacement = 0;
	
	@Override
	public String toString () {
		String output = new String ("WebRecord: ");
		output += "\nsymbol: " + symbol;
		output += "\nsymbolicRegister: " + symbolicRegister;
		output += "\nspill: " + String.valueOf(spill);
		output += "\nstackDisplacement: " + String.valueOf(stackDisplacement);
		output += "\nuses: " + uses.toString();
		output += "\ndefs: " + defs.toString();
		return output;
	}
	
	/**
	 * Prolog is a special tuple (0,-1)
	 * @return
	 */
	public boolean hasPrologDefinition () {
		final SymbolLocationInfo info = new SymbolLocationInfo (0, -1);
		for (final SymbolLocationInfo defInfo : defs) {
			if (defInfo.equals(info)) {
				return true;
			}
		}
		return false;
	}
	
	public WebRecord() {
		super();
	}
	
	public WebRecord withSymbol(final String symbol) {
		this.symbol = symbol;
		return this;
	}
	
	public WebRecord withDefs(final List<SymbolLocationInfo> defs) {
		this.defs.addAll(defs);
		return this;
	}
	
	public WebRecord withUses(final List<SymbolLocationInfo> uses) {
		this.uses.addAll(uses);
		return this;
	}
	
	public WebRecord withSymbolicRegister(final String symbolicRegister) {
		this.symbolicRegister = symbolicRegister;
		return this;
	}
	
	public void setSpill(final boolean spill) {
		this.spill = spill;
	}
	
	public void setStackDisplacement(final int stackDisplacement) {
		this.stackDisplacement = stackDisplacement;
	}
	
	public void setSymbolicRegister(final String symbolicRegister) {
		this.symbolicRegister = symbolicRegister;
	}
	
	public int getStackDisplacement() {
		return stackDisplacement;
	}
	
	public String getSymbolicRegister() {
		return symbolicRegister;
	}
	
	public void setUses (List<SymbolLocationInfo> tempUses) {
		this.uses.clear();
		this.uses.addAll(((tempUses != null)? (tempUses): (new ArrayList<SymbolLocationInfo> ())));
	}
	
	public void setDefs (final List<SymbolLocationInfo> tempDefs) {
		this.defs.clear();
		this.defs.addAll(((tempDefs != null)? (tempDefs): (new ArrayList<SymbolLocationInfo> ())));
	}
	
	public boolean getSpill() {
		return spill;
	}
	
	public List<SymbolLocationInfo> getUses() {
		return uses;
	}
	
	public List<SymbolLocationInfo> getDefs() {
		return defs;
	}
	
	public String getSymbol() {
		return symbol;
	}
	
	public String printMe () {
		String output = new String ("WebRecord representing: " + symbol 
				+ " stored in symbolicRegister: " + symbolicRegister + "\n");
		output += "The uses are:\n";
		for (final SymbolLocationInfo use : this.uses) {
			output += "( " + String.valueOf (use.returnBlockNum())
			+ " ," + String.valueOf(use.returnInsNum()) + " )\n";
		}
		output += "The defs are:\n";
		for (final SymbolLocationInfo def : this.defs) {
			output += "( " + String.valueOf (def.returnBlockNum())
			+ " ," + String.valueOf(def.returnInsNum()) + " )\n";
		}
		return output;
	}
	
	public boolean intersectsWith(final String symbol, int blocknum, int insnum) {
		final WebRecord dummy =
			new WebRecord().withSymbol(symbol).withUses(Collections.singletonList(new SymbolLocationInfo(blocknum, insnum)));
		return intersectsWith(dummy);
	}
	
 	public boolean intersectsWith(final WebRecord other) {
		if (!this.symbol.equals(other.symbol)) {
			return false;
		}

		for (final SymbolLocationInfo curUseLoc : this.uses) {
			for (final SymbolLocationInfo otherUseLoc : other.uses) {
				if (curUseLoc.equals(otherUseLoc)) {
					return true;
				}
			}
		}
		
		return false;
	}
	
 	public boolean defIntersectsWith(final String symbol, int blocknum, int insnum) {
 		final WebRecord dummy =
			new WebRecord().withSymbol(symbol).withDefs(Collections.singletonList(new SymbolLocationInfo(blocknum, insnum)));
 		return defIntersectsWith(dummy);
 	}
 	
 	public boolean defIntersectsWith(final WebRecord other) {
 		if (!this.symbol.equals(other.symbol)) {
			return false;
		}
		
		for (final SymbolLocationInfo curDefLoc : this.defs) {
			for (final SymbolLocationInfo otherDecLoc : other.defs) {
				if (curDefLoc.equals(otherDecLoc)) {
					return true;
				}
			}
		}
		
		return false;
 	}
	public void merge(final WebRecord other) {
		this.uses.addAll(other.uses);
		this.defs.addAll(other.defs);
	}
}
/**
 * POJO for building the webs and storing them in the arrayList symbolicRegisters.
 * @author sganapat
 *
 */
public static class WebBuilder {
	public WebBuilder() {
		super();
	}
	private Set<WebRecord> webs =
		new HashSet<WebRecord> ();
	
	private void populateSymbolicRegisters() {
		int i;
		for (i  = 0; i < NREGS; ++i) {
			symbolicRegisters.add(new WebRecord().withSymbol(intToReg(i)));
		}
		
		i = NREGS - 1;
		for (final WebRecord web : webs) {
			++i;
			symbolicRegisters.add(web.withSymbolicRegister(intToReg(i)));
		}
	}

	public Set<WebRecord> makeWeb(final Map<Pair<String, SymbolLocationInfo>, ArrayList<SymbolLocationInfo>> duChain) {
		int nwebs = NREGS;
		int oldnwebs = NREGS;
		for (final Map.Entry<Pair<String, SymbolLocationInfo>, ArrayList<SymbolLocationInfo>> sdu : duChain.entrySet()) {
			nwebs++;
			final WebRecord currentRecord = new WebRecord()
			.withSymbol(sdu.getKey().getFirst())
			.withDefs(Collections.singletonList(sdu.getKey().getSecond()))
			.withUses(sdu.getValue());
			webs.add(currentRecord);
		}
		
		while (oldnwebs != nwebs) {
			oldnwebs = nwebs;
			final Set<WebRecord> removeSet = new HashSet<WebRecord>();
			for (final Iterator<WebRecord> iter1 = webs.iterator(); iter1.hasNext();) {
				final WebRecord temp1 = iter1.next();
				if (removeSet.contains(temp1)) {
					continue;
				}
				for (final Iterator<WebRecord> iter2 = iter1; iter2.hasNext();) {
					final WebRecord temp2 = iter2.next();
					if (removeSet.contains(temp2)) {
						continue;
					}
					if (temp1.intersectsWith(temp2)) {
						temp1.merge(temp2);
						removeSet.add(temp2);
						--nwebs;
					}
				}
			}
			webs.removeAll(removeSet);
		}
		populateSymbolicRegisters();
		return webs;
	}
 }

/**
 * moving argument to argument registers.
 * adding symbolic register names in each frameInfo operand of LIR.
 * adding moves to replace phi functions.
 * essentially de-ssas.
 * @author sganapat
 *
 */
public static class MIRToLIRConvertor {
	
	private Map<CFGBlock, List<CFGBlock>> parentMap =
		new HashMap<CFGBlock,List<CFGBlock>> ();
	private Map<CFGBlock, List<CFGBlock>> succMap =
		new HashMap<CFGBlock, List<CFGBlock>> ();
	private Map<CFGBlock, CFGBlock> mirToLirMap = 
		new HashMap<CFGBlock, CFGBlock> ();
	private Map<CFGBlock, List<Pair<FrameInfo, FrameInfo>>> moveForPhiEliminationMap = 
		new HashMap<CFGBlock, List<Pair<FrameInfo, FrameInfo>>> ();
	
	private void handleInstruction(final CodeBlock stmt, final Set<WebRecord> webRecords,
									final CFGBlock currentMir, final CFGBlock currentLir, int blocknum, int insnum) {
		if (stmt.isDeleted) return;
		switch (stmt.opCode) {
		case CodeBlock.kADD:
		case CodeBlock.kADDA:
		case CodeBlock.kSUB:
		case CodeBlock.kMUL:
		case CodeBlock.kDIV:
		case CodeBlock.kCMP:
		{
			final FrameInfo op1 = stmt.operands.get(0);
			final FrameInfo op2 = stmt.operands.get(1);
			final FrameInfo output = stmt.outputTemporary;
			final String op1Symbol = returnSymbolicRegister(webRecords, op1, blocknum, insnum);
			final String op2Symbol = returnSymbolicRegister(webRecords, op2, blocknum, insnum);
			final String outputSymbol = returnSymbolicRegisterForDef(webRecords, output, blocknum, insnum);
			final FrameInfo op1FmInfo = op1.Clone();
			op1FmInfo.symbolicRegisterName = op1Symbol;
			final FrameInfo op2FmInfo = op2.Clone();
			op2FmInfo.symbolicRegisterName = op2Symbol;
			final FrameInfo outputFmInfo = output.Clone();
			outputFmInfo.symbolicRegisterName = outputSymbol;
			final CodeBlock theLirCode = CodeBlock.generateBinOP(op1FmInfo, op2FmInfo, stmt.opCode);
			theLirCode.label = stmt.label;
			theLirCode.outputTemporary = outputFmInfo;
			currentLir.AddStatement(theLirCode);
			break;
		}
		case CodeBlock.kNEG:
		case CodeBlock.kMOVE:
		case CodeBlock.kSTORE:
		{
			final FrameInfo op1 = stmt.operands.get(0);
			final FrameInfo output = stmt.outputTemporary;
			final String op1Symbol = returnSymbolicRegister(webRecords, op1, blocknum, insnum);
			final String outputSymbol = returnSymbolicRegisterForDef(webRecords, output, blocknum, insnum);
			final FrameInfo op1FmInfo = op1.Clone();
			op1FmInfo.symbolicRegisterName = op1Symbol;
			
			final FrameInfo outputFmInfo = output.Clone();
			outputFmInfo.symbolicRegisterName = outputSymbol;
			
			final CodeBlock theLirCode = ((stmt.opCode == CodeBlock.kNEG) ? CodeBlock.generateUnOP(op1FmInfo, stmt.opCode)
					: CodeBlock.generateMoveOrStoreOP(op1FmInfo, outputFmInfo, stmt.opCode));
			theLirCode.label = stmt.label; 
			theLirCode.outputTemporary = outputFmInfo;
			currentLir.AddStatement(theLirCode);
			break;
		}
		case CodeBlock.kBRA:
		{
			if (stmt.isCall) {
				int reg = ARGSTARTREGISTER;
				final CodeBlock dummyCall = stmt.Clone();
				dummyCall.operands.clear();
				boolean generateLabels = false;
				for (final FrameInfo op1 : stmt.operands) {
					final String op1Symbol = returnSymbolicRegister(webRecords, op1, blocknum, insnum);
					final FrameInfo op1FmInfo = op1.Clone();
					op1FmInfo.symbolicRegisterName = op1Symbol;
					if (reg == RETURNREGISTER) {
						dummyCall.operands.add(op1FmInfo);
						continue;
					}
					final String regSymbol = intToReg(reg++);
					final CodeBlock mvStmt = CodeBlock.generateMoveOrStoreOP(op1FmInfo, 
																		InterRep.globalSymTab.generateNewFrameInfo(regSymbol), CodeBlock.kMOVE);
					mvStmt.isArgPassingStatement = true;
					if (!generateLabels) {
						mvStmt.label = stmt.label;
						generateLabels = true;
					}
					currentLir.AddStatement(mvStmt);
				}
				
				dummyCall.outputTemporary.symbolicRegisterName = returnSymbolicRegisterForDef(webRecords, 
						dummyCall.outputTemporary, blocknum, insnum);
				currentLir.AddStatement(dummyCall);
			} else if (stmt.isReturn) {
				final CodeBlock actualReturn = stmt.Clone();
				if (stmt.operands != null && !stmt.operands.isEmpty()) {
					final FrameInfo op1 = stmt.operands.get(0);
					final String op1Symbol = returnSymbolicRegister(webRecords, op1, blocknum, insnum);
					final FrameInfo op1FmInfo = op1.Clone();
					op1FmInfo.symbolicRegisterName = op1Symbol;
					final String regSymbol = intToReg(RETURNVALUEREGISTER);
					CodeBlock mvStmt = CodeBlock.generateMoveOrStoreOP(op1FmInfo, 
							InterRep.globalSymTab.generateNewFrameInfo(regSymbol), CodeBlock.kMOVE);
					mvStmt.label = stmt.label;
					currentLir.AddStatement(mvStmt);
				}

				currentLir.AddStatement(actualReturn);
			} else {
				final CodeBlock actualReturn = stmt.Clone();
				actualReturn.outputTemporary = null;
				currentLir.AddStatement(actualReturn);
			}
			break;
		}
		case CodeBlock.kPHI:
		{
			scheduleMoveForPhi(stmt, webRecords, currentMir, blocknum, insnum);
			break;
		}
		case CodeBlock.kBEQ:
		case CodeBlock.kBGE:
		case CodeBlock.kBGT:
		case CodeBlock.kBLE:
		case CodeBlock.kBLT:
		case CodeBlock.kBNE:
		case CodeBlock.kLOAD:
		{
			final FrameInfo op1 = stmt.operands.get(0);
			final String op1Symbol = returnSymbolicRegister(webRecords, op1, blocknum, insnum);
			final FrameInfo op1FmInfo = op1.Clone();
			op1FmInfo.symbolicRegisterName = op1Symbol;
			final CodeBlock lirCode = CodeBlock.generateUnOP(op1FmInfo, stmt.opCode);
			lirCode.label = stmt.label;
			if (stmt.opCode != CodeBlock.kLOAD) {
				lirCode.jumpLabel = new String(stmt.jumpLabel);
				lirCode.outputTemporary = null;
			}
			currentLir.AddStatement(lirCode);
			break;
		}
		default:
		{
			throw new Error("No op code seems to match some bug in code");
		}
		}
	}
	private void scheduleMoveForPhi(final CodeBlock phiStmt, final Set<WebRecord> webRecords, 
									final CFGBlock currentMir, int blocknum, int insnum) {
		final FrameInfo output = phiStmt.outputTemporary;
		final String outputSymbolicRegister = returnSymbolicRegisterForDef(webRecords, output, blocknum, insnum);
		int j = -1;
		for (final FrameInfo input : phiStmt.operands) {
			++j;
			final String inputSymbolicRegister = returnSymbolicRegister(webRecords, input, blocknum, insnum);
			if (outputSymbolicRegister.equals(inputSymbolicRegister)) {
				continue;
			}
			final CFGBlock thePredBlock = currentMir.PredecessorList().get(j);
			final FrameInfo lhs = output.Clone();
			lhs.symbolicRegisterName = new String (outputSymbolicRegister);
			final FrameInfo rhs = input.Clone();
			rhs.symbolicRegisterName =  new String (inputSymbolicRegister);
			if (!moveForPhiEliminationMap.containsKey(thePredBlock)) {
				moveForPhiEliminationMap.put(thePredBlock, new ArrayList<Pair<FrameInfo, FrameInfo>> ());
			}
			moveForPhiEliminationMap.get(thePredBlock).add(new Pair<FrameInfo, FrameInfo> (rhs, lhs)); 
		}
	}
	
	private void remapNode(final CFGBlock mir, final CFGBlock lir) {
		if (mirToLirMap.containsKey(mir)) {
			return;
		}
		mirToLirMap.put(mir, lir);
	}
	
	private CFGBlock preprocessAndCreateLirForMir(final CFGBlock mirBlock) {
		final CFGBlock lirBlock = new CFGBlock();
		remapNode(mirBlock, lirBlock);
		final CFGBlock paren = mirBlock.GetDomParent();
		remapParentIfPossible(paren, lirBlock);
		remapSuccIfPossible(mirBlock.SuccessorList(), lirBlock);
		return lirBlock;
		
	}
	private void remapParentIfPossible(final CFGBlock oldParent, final CFGBlock newLir) {
		if (null == oldParent) {
			return;
		}
		if (mirToLirMap.containsKey(oldParent)) {
			final CFGBlock parentLir = mirToLirMap.get(oldParent);
			newLir.SetDomParent(parentLir);
			return;
		}
		if (!parentMap.containsKey(oldParent)) {
			parentMap.put(oldParent, new ArrayList<CFGBlock> ());
		}
		
		parentMap.get(oldParent).add(newLir);
	}
	private void remapSuccIfPossible (final List<CFGBlock> oldSuccs, final CFGBlock newLir) {
		for (final CFGBlock oldSucc : oldSuccs) {
			if (mirToLirMap.containsKey(oldSucc)) {
				final CFGBlock succLir = mirToLirMap.get(oldSucc);
				newLir.AddSuccessor(succLir);
			} else {
				if (!succMap.containsKey(oldSucc)) {
					succMap.put(oldSucc, new ArrayList<CFGBlock> ());
				}
				succMap.get(oldSucc).add(newLir);
			}
		}
	}
	
	private void remapAll() {
		for (final Map.Entry<CFGBlock, List<CFGBlock>> parentMapEntry : parentMap.entrySet()) {
			final CFGBlock oldParent = parentMapEntry.getKey();
			for (final CFGBlock newLir : parentMapEntry.getValue()) {
				remapParentIfPossible(oldParent, newLir); 
			}
		}
				
		for (final Map.Entry<CFGBlock, List<CFGBlock>> succMapEntry : succMap.entrySet()) {
			final CFGBlock oldSucc = succMapEntry.getKey();
			for (final CFGBlock newLir : succMapEntry.getValue()) {
				remapSuccIfPossible(Collections.singletonList(oldSucc), newLir);
			}
		}
		implementMovesForPhiElimination();
	}
	
	private void implementMovesForPhiElimination () {
		for (final Map.Entry<CFGBlock, List<Pair<FrameInfo, FrameInfo>>> phiMovesEntry : moveForPhiEliminationMap.entrySet()) {
			final CFGBlock oldBlock = phiMovesEntry.getKey();
			final CFGBlock newBlock =  mirToLirMap.get(oldBlock); //i'd rather have a crash here and fix the problem. 
			for (final Pair<FrameInfo, FrameInfo> movePair : phiMovesEntry.getValue()) {
				final CodeBlock generatedCode = CodeBlock.generateMoveOrStoreOP(movePair.getFirst(), movePair.getSecond(), CodeBlock.kMOVE);
				final List<CodeBlock> codeList = newBlock.GetStatementsList();
				int i = 0;
				for (i = codeList.size() - 1; i >= 0; --i) {
					final CodeBlock cdBlk = codeList.get(i);
					if (cdBlk.opCode == CodeBlock.kBRA && !cdBlk.isCall) {
						continue;
					} else {
						break;
					}
				}
				if (i >= codeList.size() - 1) {
					codeList.add(generatedCode);
				} else {
					codeList.add(i + 1, generatedCode);
				}
			}
		}
	}
	
	private String returnSymbolicRegister(final Set<WebRecord> webRecords, final FrameInfo symbol, final int blocknum, final int insnum) {
		if (symbol instanceof ConstFrameInfo) {
			return symbol.tempID;
		}
		for (final WebRecord webRecord : webRecords) {
			if (webRecord.intersectsWith(symbol.tempID, blocknum, insnum)) {
				return webRecord.getSymbolicRegister();
			}
		}
		return null;
	}
	
	private String returnSymbolicRegisterForDef(final Set<WebRecord> webRecords, final FrameInfo symbol, final int blocknum, final int insnum) {
		if (symbol instanceof ConstFrameInfo) {
			throw new Error("We should not have a definition point for a constant frame info");
		}
		for (final WebRecord webRecord : webRecords) {
			if (webRecord.defIntersectsWith(symbol.tempID, blocknum, insnum)) {
				return webRecord.getSymbolicRegister();
			}
		}
		return null;
	}
	
	public List<CFGBlock> modifyParamsInLirCode (final List<CFGBlock> lirCode, final Set<WebRecord> webRecords) {
		/**
		 * pre condition, no phi blocks should be present no instructions need to replicated!
		 */
		int i = -1;
		for (final CFGBlock cfgBlock : lirCode) {
			++i;
			int j = -1;
			for (final CodeBlock codeBlock : cfgBlock.GetStatementsList()) {
				++j;
				if (codeBlock.operands != null) {
					int opCount = 0;
					for (final FrameInfo fm : codeBlock.operands) {
						opCount++;
						if (2 == opCount && codeBlock.opCode == CodeBlock.kMOVE) {
							break;
						}
						final String op1Symbol = returnSymbolicRegister(webRecords, fm, i, j);
						fm.symbolicRegisterName = new String (op1Symbol);
					}
				}
				if (codeBlock.outputTemporary != null) {
					if (codeBlock.isArgPassingStatement) continue;
					final String outputSymbol = returnSymbolicRegisterForDef(webRecords, codeBlock.outputTemporary, i, j);
					codeBlock.outputTemporary.symbolicRegisterName = new String (outputSymbol);
				}
			}
		}
		return lirCode;
	}
	public List<CFGBlock> buildLIRFromMIR( final List<CFGBlock> mirCode, final Set<WebRecord> webRecords) {
		final List<CFGBlock> lirCode = new ArrayList<CFGBlock> ();
		int i = -1;
		for (final CFGBlock mirBlock : mirCode) {
			++i;
			int j = -1;
			boolean fixupLabel = false;
			final CFGBlock lirBlock = preprocessAndCreateLirForMir(mirBlock);
			lirCode.add(lirBlock);
			for (final Map.Entry<String, CodeBlock> mapEntry : mirBlock.getPhiFunctions().entrySet()) {
				++j;
				final CodeBlock phiBlock = mapEntry.getValue();
				handleInstruction(phiBlock, webRecords, mirBlock, lirBlock, i, j);
			}
			for (final CodeBlock mirCodeBlock : mirBlock.GetStatementsList()) {
				++j;
				handleInstruction(mirCodeBlock, webRecords,
						mirBlock, lirBlock, i, j);
				if (!fixupLabel) {
					final String blockLabel = mirBlock.BlockLabel();
					if (lirBlock.GetStatementsList().size() >= 1) {
						lirBlock.GetStatementsList().get(0).label = blockLabel;
						fixupLabel = true;
					}
					
				}
			}
		}
		remapAll();
		return lirCode;
	}
}

/**
 * Predicate for sorting.
 * @author sganapat
 *
 */
public static class BlockInsNumComparator implements Comparator<SymbolLocationInfo> {
	@Override
	public int compare (final SymbolLocationInfo o1, final SymbolLocationInfo o2) {
		if (o1.returnInsNum() < o2.returnInsNum ()) {
			return -1;
		} else if (o1.returnInsNum() == o2.returnInsNum()) {
			return 0;
		}
		return 1;
	}
}
/**
 * A class to compose the object that stores all info required to answer queries regarding defn overlapping.
 */
public static class BlockSymbolInfo {
	
	private int blocknum = 0;
	private Map<String, List<SymbolLocationInfo>> defMap = null;
	private Map<String, List<SymbolLocationInfo>> useMap = null;
	private Map<SymbolLocationInfo, SymbolLocationInfo> defLastUseMap = null;
	private Set<String> liveInSymbols = null;
	private Set<String> liveOutSymbols = null;
	
	@Override
	public String toString () {
		String output = new String ("BlockSymbolInfo:\n");
		output += "blocknum: " + String.valueOf (blocknum) + "\n";
		output += "defMap: " + defMap.toString() + "\n";
		output += "useMap: " + useMap.toString() + "\n";
		output += "liveInSymbols: " + liveInSymbols.toString() + "\n";
		output += "liveOutSymbols: " + liveOutSymbols.toString() + "\n";
		return output;
	}
	
	private void assertInfo () {
		if (null != defMap) {
			for (final Map.Entry<String, List<SymbolLocationInfo>> mapEntry : defMap.entrySet()) {
				final List<SymbolLocationInfo> defList = mapEntry.getValue();
				for (final SymbolLocationInfo symb : defList) {
					int blocknum = symb.returnBlockNum();
					if (this.blocknum != blocknum) {
						throw new Error ("Mismatch wrong block's data is given to us!" + symb.toString());
					}
				}
			}
		}
		
		if (null != useMap) {
			for (final Map.Entry<String, List<SymbolLocationInfo>> mapEntry : useMap.entrySet()) {
				final List<SymbolLocationInfo> useList = mapEntry.getValue();
				for (final SymbolLocationInfo symb : useList) {
					int blocknum = symb.returnBlockNum();
					if (this.blocknum != blocknum) {
						throw new Error ("Mismatch wrong block's data is given to us!" + symb.toString());
					}
				}
			}

		}
		if (null != defLastUseMap) {
			for (final Map.Entry<SymbolLocationInfo, SymbolLocationInfo> defLastUseEntry : defLastUseMap.entrySet()) {
				final int block = defLastUseEntry.getValue().returnBlockNum();
				if (this.blocknum != block) {
					throw new Error ("Mismatch wrong block's data is given to us!" + defLastUseEntry.getValue().toString());
				}
			}
		}
		
	}
	public BlockSymbolInfo (final int blocknum, final Map<String, List<SymbolLocationInfo>> defMap,
			final Map<String, List<SymbolLocationInfo>> useMap,
			final Map<SymbolLocationInfo, SymbolLocationInfo> defLastUseMap,
			final Set<String> liveInSymbols,
			final Set<String> liveOutSymbols) {
		super ();
		this.blocknum = blocknum;
		this.defMap = defMap;
		this.useMap = useMap;
		this.defLastUseMap = defLastUseMap;
		this.liveInSymbols = liveInSymbols;
		this.liveOutSymbols = liveOutSymbols;
		assertInfo ();
	}
	
	private SymbolLocationInfo findLastDefLesserThanLocation (final String symbol,
			final SymbolLocationInfo loc) {
		final List<SymbolLocationInfo> defList = this.defMap.get(symbol);
		if (null == defList || defList.isEmpty()) {
			return null;
		}
		int i = 0;
		while (i < defList.size () && defList.get(i).returnInsNum () < loc.returnInsNum()) {
			++i;
		}
		if (i >= defList.size ()) {
			return defList.get(defList.size() - 1);
		}
		return (i > 0) ? defList.get(i-1) : null;
	}
	
	public boolean definitionOverlapsWith (final SymbolLocationInfo definition, final WebRecord webRecord) {
		//check if block of definition does not match current block, if so the definition's block will handle it.
		if (definition.returnBlockNum() != this.blocknum) {
			return false;
		}
		/**
		 * If the symbol of the web record in question
		 * is present in both live in and live out. then obviously there is overlap and so we return true.
		 */
		final String webRecordSymbol = webRecord.getSymbolicRegister();
		if (liveInSymbols.contains(webRecordSymbol)
			&& liveOutSymbols.contains(webRecordSymbol)) {
			return true;
		}
		
		/**
		 * if the web record symbol is present in live in but not in live out,
		 * then true is returned iff the definition is ahead of any use and ahead
		 * of the first definition in this block for the web record or
		 * definitions of the web record is made in this block.
		 */
		if (liveInSymbols.contains(webRecordSymbol)
			&& !liveOutSymbols.contains(webRecordSymbol)) {
			for (final Map.Entry<SymbolLocationInfo, SymbolLocationInfo> defLastUseMapEntry : defLastUseMap.entrySet()) {
				final SymbolLocationInfo defKey = defLastUseMapEntry.getKey();
				final SymbolLocationInfo useVal = defLastUseMapEntry.getValue();
				if (defKey.returnInsNum() < definition.returnInsNum() 
					&& definition.returnInsNum() <= useVal.returnInsNum()) { // this is the last use so we can wlog reuse registers!
					return true;
				}
				final List<SymbolLocationInfo> useList = this.useMap.get(webRecordSymbol);
				if (useList != null) {
					for (final SymbolLocationInfo currentUse : useList) {
						if (currentUse.returnInsNum() >= definition.returnInsNum()) {
							return true;
						}
					}
				}
				return false;
			}
		}
		/**
		 * fall thru case. where
		 * no livein nor liveout is set or we have a defn before my def which
		 * obviates everything. need to find the last defn before my use and check if its
		 * last use is after me.
		 */
		final SymbolLocationInfo lastDef = findLastDefLesserThanLocation (webRecordSymbol, definition);
		if (null == lastDef) {
			return false; //no live in or live outs and no definition before our defn.
		}
		
		final SymbolLocationInfo lastUseForDef = this.defLastUseMap.get(lastDef);
		if (null == lastUseForDef) {
			return false; //dummy variable without any use just defined.
		}
		if (definition.returnInsNum() <= lastUseForDef.returnInsNum()) {
			return true; //ah we find a conflict!
		}
		return false; // the last use of this definition occurs before us.
	}
	
}
/**
 * A builder pattern class that builds BlockSymbolInfo for each blocks.
 */

public static class BlockSymbolInfoBuilder {
	private int numBlocks = 0;
	private List<CFGBlock> lirCodeBlock = null;
	private Map<Integer, Map<String, List<SymbolLocationInfo>>> use = new HashMap<Integer, Map<String,List<SymbolLocationInfo>>> ();
	private Map<Integer, Map<String, List<SymbolLocationInfo>>> def = new HashMap<Integer, Map<String,List<SymbolLocationInfo>>> ();
	private Map<Integer, BitSet> useBitmap = new HashMap<Integer, BitSet> ();
	private Map<Integer, BitSet> defBitmap = new HashMap<Integer, BitSet> ();
	private Map<String, Integer> bitPositionMap = new HashMap<String, Integer> ();
	private Map<Integer, BitSet> in = new HashMap<Integer, BitSet> ();
	private Map<Integer, BitSet> out = new HashMap<Integer, BitSet> ();
	
	public BlockSymbolInfoBuilder (final List<CFGBlock> lirCodeBlock) {
		super ();
		this.lirCodeBlock = lirCodeBlock;
		this.numBlocks = lirCodeBlock.size();
		buildUseDef ();
	}
	
	private void buildUseDef () {
		for (int i = NREGS; i < symbolicRegisters.size(); ++i) {
			final WebRecord webRecord = symbolicRegisters.get(i);
			final String symbol = webRecord.getSymbolicRegister();
			bitPositionMap.put(symbol, i - NREGS);
			for (final SymbolLocationInfo currentUse : webRecord.getUses()) {
				int blocknum = currentUse.returnBlockNum();
				if (!use.containsKey(blocknum)) {
					use.put(blocknum, new HashMap<String, List<SymbolLocationInfo>> ());
				}
				if (!use.get(blocknum).containsKey(symbol)) {
					use.get(blocknum).put(symbol, new ArrayList<SymbolLocationInfo> ());
				}
				use.get(blocknum).get(symbol).add(currentUse);
			}
			
			for (final SymbolLocationInfo currentDef : webRecord.getDefs()) {
				int blocknum = currentDef.returnBlockNum();
				if (!def.containsKey(blocknum)) {
					def.put(blocknum, new HashMap<String, List<SymbolLocationInfo>> ());
				}
				if (!def.get(blocknum).containsKey(symbol)) {
					def.get(blocknum).put(symbol, new ArrayList<SymbolLocationInfo> ());
				}
				def.get(blocknum).get(symbol).add(currentDef);
			}
		}
		
		for (final Map.Entry<Integer, Map<String, List<SymbolLocationInfo>>> mapEntry : use.entrySet()) {
			final Map<String, List<SymbolLocationInfo>> mapVal = mapEntry.getValue();
			for (final Map.Entry<String, List<SymbolLocationInfo>> entrySet : mapVal.entrySet()) {
				final List<SymbolLocationInfo> useList = entrySet.getValue();
				Collections.sort(useList, new BlockInsNumComparator ());
				System.out.println (useList);
			}
		}
		
		for (final Map.Entry<Integer, Map<String, List<SymbolLocationInfo>>> mapEntry : def.entrySet()) {
			final Map<String, List<SymbolLocationInfo>> mapVal = mapEntry.getValue();
			for (final Map.Entry<String, List<SymbolLocationInfo>> entrySet : mapVal.entrySet()) {
				final List<SymbolLocationInfo> defList = entrySet.getValue();
				Collections.sort(defList, new BlockInsNumComparator ());
				System.out.println(defList);
			}
		}
		
		/**
		 * now build the def / use bitset for each block and store it in a map.
		 * for each block, if that symbol is used in the block, then see
		 * if a def occurs earlier than any use of that symbol in that block,
		 * if it does, then erase the use of that symbol in that block.
		 */
		for (int i = 0; i < numBlocks; ++i) {
			final Map<String, List<SymbolLocationInfo>> useMap = use.get(i);
			useBitmap.put(i, new BitSet (symbolicRegisters.size() - NREGS));
			defBitmap.put (i, new BitSet (symbolicRegisters.size() - NREGS));
			if (null == useMap) {
				continue; //could be one of those empty blocks!
			}
			
			final Map<String, List<SymbolLocationInfo>> defMap = def.get(i);
			for (final Map.Entry<String, List<SymbolLocationInfo>> entry : useMap.entrySet()) {
				final String symbol = entry.getKey ();
				final Integer bitPos = bitPositionMap.get(symbol);
				final List<SymbolLocationInfo> useList = entry.getValue();
				final List<SymbolLocationInfo> defList = defMap.get(symbol);
				if (null != useList && !useList.isEmpty()) {
					if (null != defList && !defList.isEmpty()) {
						final SymbolLocationInfo firstDef = defList.get(0);
						final SymbolLocationInfo firstUse = useList.get(0);
						if (firstDef.returnInsNum() < firstUse.returnInsNum()) {
							useBitmap.get(i).clear(bitPos);
							continue;
						}
					}
					useBitmap.get(i).set(bitPos);
				}
			}
			for (final Map.Entry<String, List<SymbolLocationInfo>> entry : defMap.entrySet()) {
				final String symbol = entry.getKey();
				final List<SymbolLocationInfo> defList = entry.getValue();
				if (defList == null || defList.isEmpty()) continue;
				final Integer bitPos = bitPositionMap.get(symbol);
				defBitmap.get(i).set(bitPos);
			}
		}
	}
	
	public List<BlockSymbolInfo> constructBlockSymbolInfos () {
		final List<BlockSymbolInfo> blockSymbolInfos = new ArrayList<BlockSymbolInfo> ();
		/**
		 * do a data flow analysis and build in and out bitmaps.
		 * in --> live in of a block.
		 * out --> live out of a block.
		 */
		//initialize in and out bitmaps to all false.
		for (int i = 0; i < numBlocks; ++i) {
			in.put(i, new BitSet (symbolicRegisters.size() - NREGS));
			out.put(i,  new BitSet (symbolicRegisters.size() - NREGS));
		}
		boolean somethingChanged = false;
		do {
			somethingChanged = false;
			for (int n = 0; n < numBlocks; ++n) {
				BitSet curIn = (BitSet) useBitmap.get(n).clone();
				final BitSet tempIn = (BitSet) in.get(n).clone();
				BitSet curOut = (BitSet) out.get(n).clone ();
				final BitSet tempOut = (BitSet) curOut.clone();
				curOut.andNot (defBitmap.get(n));
				curIn.or(curOut);
				in.put(n, curIn);
				if (!in.get (n).equals( tempIn)) {
					somethingChanged = true;
				}
				curOut.clear();
				final CFGBlock currentBlock = lirCodeBlock.get(n);
				for (final CFGBlock succ : currentBlock.SuccessorList()) {
					int indx = -1;
					indx = lirCodeBlock.indexOf(succ);
					if (-1 == indx) {
						throw new Error ("Successor not present as a part of our block! something messed up!");
					}
					curOut.or(in.get(indx));
				}
				out.put(n, curOut);
				if (!out.get(n).equals(tempOut)) {
					somethingChanged = true;
				}
			}
		} while (somethingChanged);
		
		/**
		 * build the live in and live out for each block!
		 */
		for (int i = 0; i < numBlocks; ++i) {
			final Set<String> liveInSet = new HashSet<String> ();
			final Set<String> liveOutSet = new HashSet<String> ();
			final BitSet outSet = out.get (i);
			/**
			 * out set.
			 */
			for (int indx = 0; indx < outSet.size(); ++indx) {
				if (outSet.get(indx)) {
					final String symbol = symbolicRegisters.get(indx + NREGS).getSymbolicRegister();
					if (!liveOutSet.contains(symbol)) {
						liveOutSet.add(symbol);
					}
				}
			}
			/**
			 * in set!
			 */
			final BitSet inSet = this.in.get(i);
			for (int indx = 0; indx < inSet.size(); ++indx) {
				if (inSet.get(indx)) {
					final String symbol = symbolicRegisters.get(indx + NREGS).getSymbolicRegister();
					if (!liveInSet.contains(symbol)) {
						liveInSet.add(symbol);
					}
				}
			}

			final Map<String, List<SymbolLocationInfo>> blockUseMap = this.use.get(i); 
			final Map<String, List<SymbolLocationInfo>> blockDefMap = this.def.get(i);
			final Map<SymbolLocationInfo, SymbolLocationInfo> defLastUseMap =
				new HashMap<SymbolLocationInfo, SymbolLocationInfo> ();
			if (null != blockUseMap && !blockUseMap.isEmpty() 
					&& null != blockDefMap && !blockDefMap.isEmpty()) {
				for (int symbolIndex = NREGS; symbolIndex < symbolicRegisters.size(); ++symbolIndex) {
					final String currentSymbolicReg = symbolicRegisters.get(symbolIndex).getSymbolicRegister();
					final List<SymbolLocationInfo> defList = blockDefMap.get(currentSymbolicReg);
					final List<SymbolLocationInfo> useList = blockUseMap.get(currentSymbolicReg);
					if (null != defList && !defList.isEmpty() 
							&& null != useList && !useList.isEmpty()) {
						int defIndex = defList.size() - 1;
						int useIndex = useList.size() - 1;
						boolean alreadySet = false;
						while (defIndex >= 0 && useIndex >= 0) {
							if (defList.get(defIndex).returnInsNum() 
									>= useList.get(useIndex).returnInsNum()) {
								--defIndex;
								alreadySet = false;
							} else {
								if (!alreadySet) {
									defLastUseMap.put(defList.get(defIndex), useList.get(useIndex));
									alreadySet = true;
								}
								--useIndex;
							}
						}
					}
				}
			}
			//now create the block symbol info and add to the array.
			final BlockSymbolInfo blockSymbolInfo = new BlockSymbolInfo (i, blockDefMap, blockUseMap,
					defLastUseMap, liveInSet, liveOutSet);
			blockSymbolInfos.add(blockSymbolInfo);
		}
		return blockSymbolInfos;
	}
	
}

/**
 * A class which encapsulates the constraints between real and symbolic registers.
 */
public static class InterferesWithRealRegister {
	private boolean architectureRegister (int reg) {
		return reg == STACKPOINTER ||
		reg == FRAMEPOINTER ||
		reg == GLOBALPOINTER ||
		reg == ZERO;
	}
	
	private boolean volatileCallingConventionRegister (int reg) {
		return reg == RETURNREGISTER ||
		reg == RETURNVALUEREGISTER;
	}
	private boolean argumentRegister (int reg) {
		return reg >= ARGSTARTREGISTER &&
		reg < RETURNREGISTER;
	}
	
	public boolean interferesWith (int realRegister, int webLoc) {
		if ( webLoc < NREGS) {
			return true; //all real registers interfere with other real registers.
		}
		if (architectureRegister (realRegister)
			|| volatileCallingConventionRegister (realRegister)
			|| argumentRegister (realRegister)) {
			return true; 
		}
		
		return false;
	}
}

/**
 * POJ that builds the adjacency matrix of my interference graph.
 */
public static class AdjacencyMatrix {
	private List<BlockSymbolInfo> blockSymbolInfos = new ArrayList<BlockSymbolInfo> ();
	private InterferesWithRealRegister interferesWith = null;
	private boolean [][] adjacencyMatrix = null;
	private int nwebs = 0;
	public AdjacencyMatrix (final List<CFGBlock> lirCode) {
		super ();
		
		adjacencyMatrix = new boolean[symbolicRegisters.size()][symbolicRegisters.size()];
		interferesWith = new InterferesWithRealRegister ();
		final FixupSymbolicRegisters fixup = new FixupSymbolicRegisters (lirCode);
		fixup.doFixup();
		nwebs = symbolicRegisters.size();
		final BlockSymbolInfoBuilder builderPattern = new BlockSymbolInfoBuilder (lirCode);
		blockSymbolInfos = builderPattern.constructBlockSymbolInfos();
	}
	
	public boolean isAdjacent (int i, int j) {
		return adjacencyMatrix[Math.max(i, j)][Math.min(i, j)];
	}
	
	private boolean liveAt (final SymbolLocationInfo definition, final WebRecord webRecord) {
		for (final BlockSymbolInfo blockSymbolInfo : blockSymbolInfos) {
			if (blockSymbolInfo.definitionOverlapsWith(definition, webRecord)) {
				return true;
			}
		}
		return false;
	}
	
	public List<BlockSymbolInfo> returnBlockSymbolInfos () {
		return this.blockSymbolInfos;
	}
	
	
	public void buildAdjacencyMatrix () {
		for (int i = 1; i < nwebs; ++i) {
			for (int j = 0; j < i; ++j) {
				adjacencyMatrix[i][j] = false; //initialize all elements of the lower triangular matrix.
			}
		}
		
		for (int i = 1; i < NREGS; ++i) {
			for (int j = 0; j < i; ++j) {
				adjacencyMatrix[i][j] = true;
			}
		}
		
		for (int i = NREGS; i < nwebs; ++i) {
			for (int j = 0; j < NREGS; ++j) {
				if (interferesWith.interferesWith(j, i)) {
					adjacencyMatrix[i][j] = true;
				}
			}
			
			for (int j = NREGS; j < nwebs; ++j) {
				if (j == i) continue;
				for (final SymbolLocationInfo definition : symbolicRegisters.get(i).getDefs()) {
					if (liveAt (definition, symbolicRegisters.get(j))) {
						adjacencyMatrix[Math.max(i, j)][Math.min(i, j)] = true;
					}
				}
			}
		}
	}
	
	public void mergeAndRemove (int targetindex, int sourceindex) {
		for (int p = 0; p < nwebs; ++p) {
			if (isAdjacent (p, sourceindex)) {
				this.adjacencyMatrix[Math.max(p, targetindex)][Math.min(p, targetindex)] = true;
			}
			this.adjacencyMatrix[Math.max(p, sourceindex)][Math.min(p, sourceindex)]
			           = this.adjacencyMatrix[Math.max(p, nwebs - 1)][Math.min(p, nwebs - 1)];
		}
		--nwebs;
	}
	
	public String serializeGraphToString () {
		String outputString = new String ("Interference Graph:	");
		for (int i = NREGS; i < nwebs; ++i) {
			for (int j = NREGS; j < i; ++j) {
				///print the uses and defs of i.
				if (adjacencyMatrix[i][j]) {
					outputString += "The symbolic registers represented with indices: "
						+ String.valueOf(i) + " and " +  String.valueOf(j) 
						+ " overlaps and their contents are:\n";
					outputString += symbolicRegisters.get(i).printMe() + "\n";
					outputString += symbolicRegisters.get(j).printMe() + "\n";
				}
			}
		}
		outputString += "Finished printing all interferences\n";
		return outputString;
		
	}
}

/**
 * POJO to fixup the def use chains to account for any instruction deleted due to coalescing and so forth.
 * @author sganapat
 *
 */
public static class FixupSymbolicRegisters {
	final Map<String, List<SymbolLocationInfo>> useMap = new HashMap<String, List<SymbolLocationInfo>> ();
	final Map<String, List<SymbolLocationInfo>> defMap = new HashMap<String, List<SymbolLocationInfo>> ();
 	public FixupSymbolicRegisters (final List<CFGBlock>  lirCode) {
		super ();
		int i = -1;
		for (final CFGBlock lir : lirCode) {
			++i;
			int j = -1;
			for (final CodeBlock code : lir.GetStatementsList()) {
				++j;
				if (code.isDeleted) {
					continue;
				}
				if (code.operands != null) {
					int argCount = 0;
					for (final FrameInfo arg : code.operands) {
						++argCount;
						if (argCount == 2 && code.opCode == CodeBlock.kMOVE) break;
						final String symbolicRegister = arg.symbolicRegisterName;
						if (null == symbolicRegister || symbolicRegister.isEmpty()) {
							continue;
						}
						if (!useMap.containsKey(symbolicRegister)) {
							useMap.put(symbolicRegister, new ArrayList<SymbolLocationInfo> ());
						}
						useMap.get(symbolicRegister).add (new SymbolLocationInfo (i, j));
						if (code.opCode == CodeBlock.kMOVE) {
							break;
						}
					}
				}
				
				if (code.outputTemporary != null) {
					final String symbolicRegister = code.outputTemporary.symbolicRegisterName;
					if (null == symbolicRegister) {
						continue;
					}
					if (!defMap.containsKey (symbolicRegister)) {
						defMap.put(symbolicRegister, new ArrayList<SymbolLocationInfo> ());
					}
					defMap.get(symbolicRegister).add(new SymbolLocationInfo (i, j));
				}
			}
		}
	}
 	
 	private boolean isFunArg (final String argname) {
 		final String fnName = InterRep.globalSymTab.GetOptimizeScope();
 		final List<FrameInfo> argList = InterRep.globalSymTab.getFormalsInfo(fnName);
 		if (null == argList) {
 			return false;
 		}
 		
 		for (final FrameInfo fm : argList) {
 			final String tempid = fm.tempID;
 			if (null == tempid) continue;
 			if (tempid.equals (argname)) {
 				return true;
 			}
 		}
 		
 		return false;
 	}
 	
 	public void doFixup () {
 		for (final ListIterator<WebRecord> listIter = symbolicRegisters.listIterator(NREGS); listIter.hasNext(); ) {
 			final WebRecord webRecord = listIter.next();
 			final String symbolicRegister = webRecord.getSymbolicRegister();
 			final List<SymbolLocationInfo> useList = useMap.get(symbolicRegister);
 			List<SymbolLocationInfo> defList = defMap.get(symbolicRegister);
 			if ((null == useList || useList.isEmpty()) 
 				&& (null == defList || defList.isEmpty())) {
 				listIter.remove();
 				continue;
 			}
 			if (webRecord.hasPrologDefinition() 
 				&& this.isFunArg(webRecord.getSymbol())) {
 				if (null == defList) {
 					defList = new ArrayList<SymbolLocationInfo> ();
 				}
 				defList.add(new SymbolLocationInfo (0, -1));
 			}
 			webRecord.setUses(useList);
 			webRecord.setDefs(defList);
 		}
 	}
}

/**
 * POJ to coalesce symbolic registers
 * 
 */
public static class CoalesceSymbolicRegisters {
	private AdjacencyMatrix adjacencyMatrix = null;
	private Map<String, Integer> bitPositionMap = new HashMap<String, Integer> ();
	private List<CFGBlock> lirCode = null;
	public CoalesceSymbolicRegisters (final AdjacencyMatrix adjacencyMatrix, final List<CFGBlock> lirCode) {
		super ();
		this.lirCode = lirCode;
		this.adjacencyMatrix = adjacencyMatrix;
		
		int pos = 0;
		
		for (int i = NREGS; i < symbolicRegisters.size(); ++i) {
			final String symbol = symbolicRegisters.get(i).getSymbolicRegister();
			bitPositionMap.put(symbol, pos++);
		}
		
	}
	
	private boolean isMovInstruction(final CodeBlock cdBlk) {
		return cdBlk.opCode == CodeBlock.kMOVE;
	}
	
	private boolean isSymbolicRegister(final FrameInfo fmInfo) {
		if (null == fmInfo.symbolicRegisterName) {
			return false;
		}
		return this.bitPositionMap.containsKey(fmInfo.symbolicRegisterName);
	}
	
	private boolean noStoresBelow (final FrameInfo fmInfo, final CFGBlock currentBlock, int insnum, final Set<CFGBlock> visitedBlocks) {
		if (visitedBlocks.contains(currentBlock)) {
			return true;
		}
		final List<CodeBlock> blockInsList = currentBlock.GetStatementsList();
		for (int i = insnum + 1; i < blockInsList.size(); ++i) {
			final CodeBlock curBlock = blockInsList.get(i);
			final FrameInfo opTemp = ((curBlock.opCode == CodeBlock.kMOVE) ? curBlock.operands.get(1) 
					: curBlock.outputTemporary);
			if (opTemp != null) {
				if (equalFrameInfos (opTemp, fmInfo)) {
					return false;
				}
			}
		}
		visitedBlocks.add(currentBlock);
		boolean runningVal = true;
		for (final CFGBlock succ : currentBlock.SuccessorList()) {
			runningVal = runningVal && noStoresBelow (fmInfo, succ, -1, visitedBlocks);
		}
		return runningVal;
	}
	
	private boolean equalFrameInfos (final FrameInfo fm1, final FrameInfo fm2) {
		if (null == fm1 || null == fm2) {
			return false;
		}
		final String symbolicRegister1 = fm1.symbolicRegisterName;
		final String symbolicRegister2 = fm2.symbolicRegisterName;
		return symbolicRegister1 != null && symbolicRegister2 != null && symbolicRegister1.equals (symbolicRegister2);
	}
	
	public void replaceRhsWithLhs (final FrameInfo rhs, final FrameInfo lhs) {
		for (final CFGBlock lir : lirCode) {
			for (final CodeBlock code : lir.GetStatementsList()) {
				if (null != code.operands) {
					for (int i = 0; i < code.operands.size(); ++i) {
						final FrameInfo fm = code.operands.get(i);
						if (equalFrameInfos(fm, rhs)) {
							code.operands.set(i, lhs.Clone());
						}
					}
				}
				if (null != code.outputTemporary) {
					if (equalFrameInfos (code.outputTemporary, rhs)) {
						code.outputTemporary = lhs.Clone();
					}
				}
				
			}
		}
	}
	
	public Pair<List<CFGBlock>, Boolean> coalesceRegisters() {
		boolean coalesced = false;
		for (final Iterator<CFGBlock> lirBlockIter = lirCode.iterator(); lirBlockIter.hasNext(); ) {
			final CFGBlock lirBlock = lirBlockIter.next();
			int j = -1;
			String labelToFixUp = null;
			for (final Iterator<CodeBlock> codeBlockIter = lirBlock.GetStatementsList().iterator(); codeBlockIter.hasNext(); )  {
				++j;
				final CodeBlock codeBlock = codeBlockIter.next();
				if (labelToFixUp != null) {
					codeBlock.label = new String (labelToFixUp);
					labelToFixUp = null;
				}
				if (isMovInstruction (codeBlock)) {
					final FrameInfo rhs = codeBlock.operands.get(0);
					final FrameInfo lhs = codeBlock.operands.get(1); 
					if (isSymbolicRegister (rhs)
						&& isSymbolicRegister (lhs)) {
						final int bitPos1 = this.bitPositionMap.get(rhs.symbolicRegisterName) + NREGS;
						final int bitPos2 = this.bitPositionMap.get(lhs.symbolicRegisterName) + NREGS;
						if (!this.adjacencyMatrix.isAdjacent(bitPos1, bitPos2)
							|| (this.noStoresBelow(rhs, lirBlock, j, new HashSet<CFGBlock> ())
								&& noStoresBelow(lhs, lirBlock, j, new HashSet<CFGBlock> ()))) {
							replaceRhsWithLhs (rhs, lhs);
							if (j == 0) {
								labelToFixUp = new String (codeBlock.label);
							}
							codeBlockIter.remove();
							coalesced = true;
							adjacencyMatrix.mergeAndRemove(bitPos2, bitPos1);
							final Pair<String, Integer> modifiedPair = 
								mergeAndRemoveFromSymbolicRegisters (symbolicRegisters.get(bitPos2), symbolicRegisters.get(bitPos1));
							int newBitPos = modifiedPair.getSecond() - NREGS;
							bitPositionMap.put(modifiedPair.getFirst(), newBitPos);
						}
					}
				}
				
			}
		}
		return new Pair<List<CFGBlock>, Boolean> (lirCode, coalesced);
	}	
}

/**
 * POJ for an element of the adjacency list. 
 */
public static class AdjacencyListElement {
	private int pos = -1;
	private Integer color = null;
	private Integer disp = null;
	private int spcost = 0;
	private boolean spill = false;
	private Set<Integer> adjacencyList = new HashSet<Integer> ();
	private Set<Integer> removedElements = new HashSet<Integer> ();
	
	public void setSpill ( final boolean spill) {
		this.spill = spill;
	}
	
	public boolean getSpill () {
		return this.spill;
	}
	
	@Override
	public String toString () {
		String output = new String ("AdjacencyListElement: ");
		if (pos < NREGS) {
			output += "The real register is: " + "R" + String.valueOf(pos);
		} else {
			output += "The symbolic register is: " + symbolicRegisters.get(pos).getSymbolicRegister();
		}
		
		output += " The color assigned is: " + (color == null? "unassigned" : String.valueOf(color));
		output += " The spill slot in the stack is " + (disp == null? "undefined" : String.valueOf(disp));
		output += " The associated cost to spill is " + String.valueOf (spcost);
		output += " The adjacency list of this element has : ";
		for (final int i : adjacencyList) {
			if (symbolicRegisters.get(i).getSymbolicRegister() == null) continue;
			output += " " + symbolicRegisters.get(i).getSymbolicRegister() + " ";
		}
		output += " The following elements were pruned from this list: " +  removedElements.toString();
		
		return output;
	}
	
	public void removeInterference (final int i) {
		if (adjacencyList.contains(i)) {
			adjacencyList.remove(i);
			removedElements.add(i);
		}
	}
	
	public void removeAllInterferences () {
		removedElements.addAll(adjacencyList);
		adjacencyList.clear();
	}
	
	public AdjacencyListElement (final int pos) {
		super ();
		this.pos = pos;
		if (this.pos < NREGS) {
			spcost = Integer.MAX_VALUE;
		} else {
			spcost = 0;
		}
	}
	
	public Integer getColor () {
		return color;
	}
	
	public AdjacencyListElement withColor(final int color) {
		this.color = color;
		return this;
	}
	
	public Integer getDisp() {
		return disp;
	}
	
	public AdjacencyListElement withDisp (final int disp) {
		this.disp = disp;
		return this;
	}
	
	public int getSpillCost() {
		return spcost;
	}
	
	public AdjacencyListElement withSpillCost (final int spcost) {
		this.spcost = spcost;
		return this;
	}
	
	public Set<Integer> getAdjacencyList () {
		return this.adjacencyList;
	}
	
	public int getAdjLength () {
		return this.adjacencyList.size();
	}
	
	public Set<Integer>  getPrunedElements () {
		return this.removedElements;
	}
	
	public void insertIntoAdjacencyList (final int newNeighbour) {
		if (removedElements.contains(newNeighbour)) {
			removedElements.remove(newNeighbour);
		}
		adjacencyList.add(newNeighbour);
	}
	
	public void removeFromAdjacencyList (final int prunedNeighbour) {
		if (adjacencyList.contains(prunedNeighbour)) {
			adjacencyList.remove(prunedNeighbour);
		}
		removedElements.add(prunedNeighbour);
	}
}

/**
 * POJ representing the InterferenceGraph from the adjacency matrix!
 */
public static class InterferenceGraph {
	private AdjacencyMatrix adjacencyMatrix = null;
	private List<AdjacencyListElement> adjacencyList = new ArrayList<AdjacencyListElement> ();
	private Map<String, Integer> symbolicRegisterToPositionMap = new HashMap<String, Integer> ();
 	public InterferenceGraph(final AdjacencyMatrix adjacencyMatrix) {
		super ();
		this.adjacencyMatrix = adjacencyMatrix;
		for (int i = 0; i < symbolicRegisters.size(); ++i) {
			final AdjacencyListElement adjListElement =
				new AdjacencyListElement (i);
			adjacencyList.add(adjListElement);
			if (i >= NREGS) {
				symbolicRegisterToPositionMap.put(symbolicRegisters.get(i).getSymbolicRegister(), i);
			}
		}
		buildListFromMatrix ();
	}
 	
 	private Map<CFGBlock, Integer> depthMap = new HashMap<CFGBlock, Integer> ();
 	private int timestamp = 0;
 	private int findDepthForTS (final List<Integer> arr, int num) {
 		if (arr.size() <= 0) {
 			return 0;
 		}
 		int i = 0;
 		for ( ; i < arr.size() && arr.get(i) <= num; ++i);
 		return i;
 	}
 	
 	private void depthFromCode(final CFGBlock root, 
 			final Map<CFGBlock, Integer> greyMap, final Map<CFGBlock, Integer> blackMap, final List<Integer> sortedTimestamps) {
 		if (null == root) {
 			return;
 		}
 		if (greyMap.containsKey(root)) {
 			sortedTimestamps.add(greyMap.get(root));
 			Collections.sort(sortedTimestamps);
 			return;
 		} else if (blackMap.containsKey(root)) {
 			//either a join block or base of the loop block.
 			//or more subtly could be the block containing a return stmt
 			//within the loop but this block will be executed only once if it is taken
 			//so we can disregard it!
 			return;
 		}
 		
 		int ts = timestamp;
 		greyMap.put(root, timestamp++);
 		depthMap.put(root, 0); //initialize depth to zero!
 		for (final CFGBlock succ : root.SuccessorList()) {
 			depthFromCode (succ, greyMap, blackMap, sortedTimestamps);
 		}
 		depthMap.put (root, depthMap.get(root) + findDepthForTS(sortedTimestamps, ts));
 		if (sortedTimestamps.contains(ts)) {
 			int indx = sortedTimestamps.indexOf(ts);
 			sortedTimestamps.remove(indx);
 		}
 		greyMap.remove(root);
 		blackMap.put(root, ts);
 	}
 	
 	public void buildSpillCostFromCodeBlocks (final List<CFGBlock> codeBlocks) {
 		depthFromCode (codeBlocks.get(0), new HashMap<CFGBlock, Integer> (),
 				new HashMap<CFGBlock, Integer> (), new ArrayList<Integer> ());
 		for (final CFGBlock cfgBlock : codeBlocks) {
 			final int depth = this.depthMap.get(cfgBlock);
 			for (final CodeBlock codeBlock : cfgBlock.GetStatementsList()) {
 				
 				if (codeBlock.operands != null) {
 					int argCount = 0;
 					for (final FrameInfo fmInfo : codeBlock.operands) {
 						++argCount;
 						if (codeBlock.opCode == CodeBlock.kMOVE && 2 == argCount) {
 							break;
 						}
 						if (fmInfo instanceof ConstFrameInfo) {
 							continue;
 						}
 						
 						final String symbolicRegister = fmInfo.symbolicRegisterName;
 						if (null == symbolicRegister) {
 							continue;
 						}
 						final Integer pos =  this.symbolicRegisterToPositionMap.get(symbolicRegister);
 						if (null ==  pos) {
 							continue;
 						}
 						final AdjacencyListElement elem = this.adjacencyList.get(pos);
 							
 						elem.withSpillCost(elem.getSpillCost() + (int) Math.pow((double) 10, (double) depth));
 						
 						if (codeBlock.opCode == CodeBlock.kMOVE) {
 							break;
 						}
 					} 
 				}
 				if (codeBlock.outputTemporary != null && !codeBlock.isArgPassingStatement) {
 					final String symbolicRegister = codeBlock.outputTemporary.symbolicRegisterName;
					if (null == symbolicRegister) {
						continue;
					}
					final Integer pos =  this.symbolicRegisterToPositionMap.get(symbolicRegister);
					if (null ==  pos) {
						continue;
					}
					final AdjacencyListElement elem = this.adjacencyList.get(pos);
						
					elem.withSpillCost(elem.getSpillCost() + (int) Math.pow((double) 10, (double) depth));
 				}
 			}
 		}
 	}
 	
 	private void buildListFromMatrix () {
 		for (int i = 1; i < symbolicRegisters.size(); ++i) {
 			for (int j = 0; j < symbolicRegisters.size() - 1; ++j) {
 				if (j == i) continue;
 				if (adjacencyMatrix.isAdjacent(i, j)) {
 					adjacencyList.get(i).insertIntoAdjacencyList(j);
 					adjacencyList.get(j).insertIntoAdjacencyList(i);
 				}
 			}
 		}
 	}
 	
 	@Override
 	public String toString () {
 		String output = new String ("Inteference Graph: ");
 		for (final AdjacencyListElement elem : adjacencyList) {
 			output += "[ " + elem.toString() + " ]\n";	
 		}
 		
 		return output;
 	}
 	final int[] AvblRegisters = new int[32];
 	            
 	final List<Integer> stack = new ArrayList<Integer> ();
 	
 	public void pruneGraph () {
 		
 		final List<Integer> inputSet = new ArrayList<Integer> ();
 		for (int i = 0; i < symbolicRegisters.size(); ++i) {
 			inputSet.add(i);
 		}
 		while (!inputSet.isEmpty()) {
			for (ListIterator<Integer> listIter = inputSet.listIterator(); listIter.hasNext(); ) {
				final int i = listIter.next();
				final int len = this.adjacencyList.get(i).getAdjLength();
				if (len < AvblRegisters.length) {
					stack.add(i);
					listIter.remove();
					adjustNeighbours (i);
				}
			}
 			if (!inputSet.isEmpty()) {
 				int spillCost = Integer.MAX_VALUE;
 				Integer spillNode = -1;
 				for (ListIterator<Integer> listIter = inputSet.listIterator(); listIter.hasNext(); ) {
 					final Integer i = listIter.next();
 					final int len = this.adjacencyList.get(i).getAdjLength();
 					final int nodeSpillCost = this.adjacencyList.get(i).getSpillCost();
 					if (len > 0
 						&& nodeSpillCost / len <= spillCost) {
 						spillNode = i;
 						spillCost = nodeSpillCost / len;
 					}
 				}
 				if (spillNode != -1) {
 					stack.add(spillNode);
 	 				adjustNeighbours (spillNode);
 	 				inputSet.remove((Object) spillNode);
 				}
 				
 			}
 		}
 	}
 	
 	private void adjustNeighbours (final int i) {
 		final Set<Integer> interferences = this.adjacencyList.get(i).getAdjacencyList();
 		for (final int k : interferences) {
 			if (k == i) {
 				continue;
 			}
 			this.adjacencyList.get(k).removeInterference(i);
 		}
 		this.adjacencyList.get(i).removeAllInterferences();
 	}
 	
 	private int minColor (int r) {
 		final List<Integer> tempAvblRegs = new ArrayList<Integer> ();
 		for (int i = 0; i < AvblRegisters.length; ++i) {
 			tempAvblRegs.add(i);
 		}
 		
 		final Set<Integer> interferences = this.adjacencyList.get(r).getAdjacencyList();
 		final Set<Integer> removedInterferences = this.adjacencyList.get(r).getPrunedElements();
 		for (final int i : interferences) {
 			final Integer color = this.adjacencyList.get(i).getColor();
 			if (null != color) {
 				tempAvblRegs.remove((Object) color);
 			}
 		}
 		for (final int i : removedInterferences) {
 			final Integer color = this.adjacencyList.get(i).getColor();
 			if (null != color) {
 				tempAvblRegs.remove((Object) color);
 			}
 		}
 		return tempAvblRegs.isEmpty() ? -1 : tempAvblRegs.get(0);
 	}
 	
 	public boolean assignRegisters () {
 		boolean success = true;
 		while (!stack.isEmpty()) {
 			int r = stack.get(stack.size() - 1);
 			stack.remove(stack.size() - 1);
 			int c = minColor (r);
 			if (c >= 0) {
 				if (r < NREGS) {
 					AvblRegisters[c] = r;
 				}
 				this.adjacencyList.get(r).withColor(c); 
 			} else {
 				this.adjacencyList.get(r).setSpill(true);
 				success = false;
 			}
 		}
 		return success;
 	}
 	
 	public List<CFGBlock> modifyCode (final List<CFGBlock> lirCode) {
 		for (final CFGBlock cfgBlock : lirCode) {
 			for (final CodeBlock codeBlock : cfgBlock.GetStatementsList()) {
 				if (codeBlock.operands != null) {
 					int argCount = 0;
 					for (final FrameInfo fmInfo : codeBlock.operands) {
 						++argCount;
 						if (codeBlock.opCode == CodeBlock.kMOVE && 2 == argCount) {
 							continue;
 						}
 						if (fmInfo instanceof ConstFrameInfo) {
 							continue;
 						}
 						final String symbolicRegister = fmInfo.symbolicRegisterName;
 						if (null == symbolicRegister) {
 							continue;
 						}
 						final Integer pos = this.symbolicRegisterToPositionMap.get(symbolicRegister);
 						if (null == pos) {
 							continue;
 						}
 						final int color = this.adjacencyList.get(pos).getColor();
 						final String actualReg = intToReg (AvblRegisters[color]);
 						
 						fmInfo.registerPosition = new String (actualReg);
 						if (codeBlock.opCode == CodeBlock.kMOVE) {
 							break;
 						}
 					}
 				}
 				if (codeBlock.outputTemporary != null) {
 					final FrameInfo fmInfo = codeBlock.outputTemporary;
 					final String symbolicRegister = fmInfo.symbolicRegisterName;
					if (null == symbolicRegister) {
						continue;
					}
					final int pos = this.symbolicRegisterToPositionMap.get(symbolicRegister);
					final int color = this.adjacencyList.get(pos).getColor();
					final String actualReg = intToReg (AvblRegisters[color]);
					
					fmInfo.registerPosition = new String (actualReg);
 				}
  			}
 		}
 		return lirCode;
 	}
 	private int disp = 4;
 	Map<String, Integer> argNames = null;
 	private void computeDisp (final int r) {
 		final String symbol = symbolicRegisters.get(r).getSymbol();
 		if (argNames == null) {
 			argNames = new HashMap<String, Integer> ();
 	 		final String fnName = InterRep.globalSymTab.GetOptimizeScope();
 	 		final List<FrameInfo> args = InterRep.globalSymTab.getFormalsInfo(fnName);
 	 		if (null != args) {
 	 			int i = 0;
 	 			for (final FrameInfo arg : args) {
 	 				++i;
 	 				argNames.put(arg.tempID, i);
 	 			}
 	 		}
 		}
 		if (argNames.containsKey(symbol)) {
 			if (null != this.adjacencyList.get(r).getDisp()) return; //already computed.
 			if (null == this.adjacencyList.get(r).getColor()) {
 				this.adjacencyList.get(r).withDisp(-argNames.get(symbol)); //we use -ve displacements for function arguments.
 			}
 			return;
 		}
 		if (null != this.adjacencyList.get(r).getDisp()) return; //already computed.
	 	if (null == this.adjacencyList.get(r).getColor()) {
	 		this.adjacencyList.get(r).withDisp(disp);
	 		disp += 4;
	 	}
 	}
 	
 	public List<CFGBlock> genSpillCode (final List<CFGBlock> lirCode) {
 		int i  = -1;
 		for (final CFGBlock cfgBlock : lirCode) {
 			++i;
 			boolean noprev = true;
 			for (ListIterator<CodeBlock> listIter = cfgBlock.GetStatementsList().listIterator(); listIter.hasNext(); ) {
 				CodeBlock currentCode = listIter.next();
 				if (currentCode.operands != null) {
 					final Set<Integer> alreadySpilled = new HashSet<Integer> ();
 					for (int k = 0; k < currentCode.operands.size(); ++k) {
 						if (k > 0 && currentCode.opCode == CodeBlock.kMOVE) break;
 						final FrameInfo fm = currentCode.operands.get(k);
 						final String symbolicRegister = fm.symbolicRegisterName;
 						if (null == symbolicRegister) {
 							continue;
 						}
 						Integer pos = this.symbolicRegisterToPositionMap.get(symbolicRegister);
 						if (null == pos) {
 							continue;
 						}
 						if (this.adjacencyList.get(pos).getSpill() == false) continue;
 						if (alreadySpilled.contains(pos)) continue;
 						alreadySpilled.add(pos);
 						computeDisp (pos);
 						int displacement = this.adjacencyList.get(pos).getDisp();
 						currentCode = listIter.previous();
 						final FrameInfo addressInfo = InterRep.globalSymTab.generateConstantFrameInfo(displacement);
 						final CodeBlock spillCode = CodeBlock.generateUnOP(addressInfo, CodeBlock.kLOAD);
 						if (noprev) {
 							spillCode.label = new String (currentCode.label);
 							noprev = false;
 						}
 						spillCode.outputTemporary = fm.Clone();
 						listIter.add(spillCode);
 						listIter.next();
 					}
 				}
 				if (currentCode.outputTemporary != null) {
 					final FrameInfo fm = currentCode.outputTemporary;
					final String symbolicRegister = fm.symbolicRegisterName;
					if (null == symbolicRegister) {
						continue;
					}
					int pos = this.symbolicRegisterToPositionMap.get(symbolicRegister);
					if (this.adjacencyList.get(pos).getSpill() == false) continue;
					computeDisp (pos);
					int displacement = this.adjacencyList.get(pos).getDisp();
					currentCode = listIter.previous();
					final FrameInfo addressInfo = InterRep.globalSymTab.generateConstantFrameInfo(displacement);
					final CodeBlock spillCode = CodeBlock.generateMoveOrStoreOP(fm.Clone(), addressInfo, CodeBlock.kSTORE);
					listIter.add(spillCode);
 				}
 			}
 		}
 		return lirCode;
 	}
}
}

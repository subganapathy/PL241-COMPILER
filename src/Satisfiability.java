
import java.util.BitSet;
import java.util.Arrays;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
/**
 * 
 * This is the satisfiability class , 
 * its constructor takes nb, the number of terms
 * nc, the number of clauses
 * clauseSet, the actual clauses.
 * data structures:
 * clauseSet --> the original passed input set of clauses, consists of entries like 1 -2 3 i.e. a1 OR ~a2 OR a3
 * watchList --> the set of values such that the clause can never be true i.e. for the above clause the watch list
 * is -1 , 2 and -3. -1 --> represented by bit position NB + 0. in general un complemented state is represented by val - 1
 * and complemented state is NB + val - 1
 * clauseChoices  ---> the list of valid choices that may be made for each clause.
 */
public class Satisfiability {
private int NB = 3;
private int NC = 3;
private int[] terms = new int[] { 1, 2, 3};
private String[] clauseSet = null;
private BitSet[] watchList = null;
private Map<Integer, List<Integer>> clauseChoices = new HashMap<Integer, List<Integer>> ();
public Satisfiability (int nb, int nc, String[] clauseSet) {
	super ();
	NB = nb;
	NC = nc;
	terms = new int[NB];
	for (int i  = 0; i < NB; ++i) {
		terms[i] = i + 1;
	}
	this.clauseSet = clauseSet;
	watchList = new BitSet[NC];
	Arrays.fill (watchList, createDoubleBitSet()); //bits are all cleared by default.
	int i = -1;
	for (final String clause : this.clauseSet) {
		i++;
		buildWatchListAndClauseChoice (clause, i);
	}
} 
private BitSet chosenTerms = null;

private BitSet createSingleBitSet () {
	final BitSet op = new BitSet(NB);
	op.clear();
	return op;
}
private void setDoubleBit (final BitSet bt, int index) {
	bt.set(index);
	bt.clear(index + NB);
}

private void clearDoubleBit (final BitSet bt, int index) {
	bt.clear(index);
	bt.set(index + NB);
}

private BitSet createDoubleBitSet () {
	final BitSet op = new BitSet (2 * NB);
	op.clear();
	return op;
}
/**
 * checks whehter this clause can be solved if we choose the term represented by index == termChoice.
 * we reuse watch list here. if watch list un-complemented bit is set --> our term choice is a complement, 
 * why? because watch list stores the conflicting states which implies the clause can never be true so its opposite is true.
 * @param clauseIndex
 * @param termChoice
 * @return
 */
private boolean solvesThisClause (final int clauseIndex, int termChoice) {
	if (runningSoln.get(termChoice + NB)) {
		termChoice += NB;
	}
	return !(watchList[clauseIndex].get(termChoice));
}

/**
 * conflict as we discussed in morning.
 * @param clauseIndex
 * @return
 */
private boolean conflictsWithOthers (final int clauseIndex) {
	for (int i = clauseIndex + 1; i < clauseSet.length; ++i) {
		BitSet clonedSoln = (BitSet)runningSoln.clone();
		clonedSoln.and(watchList[i]);
		if (clonedSoln.equals(watchList[i])) {
			return true;
		}
	}
	return false;
}

private void updateRunningSoln (final int clauseIndex, final int termChoice) {
	if (!watchList[clauseIndex].get(termChoice)) {
		setDoubleBit (runningSoln, termChoice);
	} else {
		clearDoubleBit (runningSoln, termChoice);
	}
}

private boolean recurs(int currentClauseIndex) {
	if (currentClauseIndex >= clauseSet.length) {
		return true;
	}
	final List<Integer> clauseChoiceList = clauseChoices.get(currentClauseIndex);
	Integer prevChoice = null;
	for (final int clauseChoice : clauseChoiceList) {
		if (prevChoice != null) {
			chosenTerms.clear(prevChoice);
			runningSoln.clear(prevChoice);
			runningSoln.clear(prevChoice + NB);
			prevChoice = null;
		}
		if (chosenTerms.get(clauseChoice) && !solvesThisClause(currentClauseIndex, clauseChoice)) {
			continue;
		} else if (!chosenTerms.get(clauseChoice)) {
			chosenTerms.set(clauseChoice);
			prevChoice = new Integer(clauseChoice);
			updateRunningSoln (currentClauseIndex, clauseChoice);
		}
		
		if (conflictsWithOthers (currentClauseIndex)) {
			continue;
		}
		if (recurs (currentClauseIndex + 1)) {
			return true;
		}
	}
	return false;
}

private BitSet runningSoln = null;

public String[] checkForSolution () {

	runningSoln = createDoubleBitSet ();
	chosenTerms = createSingleBitSet ();
	
	if (!recurs(0)) {
		return null;
	}
	
	final String[] soln = new String[NB];
	for (int i = 0; i < soln.length; ++i) {
		if (runningSoln.get(i)) {
			soln[i] = String.valueOf(i + 1);
		} else {
			soln[i] = String.valueOf(-(i + 1));
		}
	}
	return soln;
}
private void buildWatchListAndClauseChoice (final String clause, final int clauseIndex) {
	boolean prevMinus = false;
	final char[] clauseArray = clause.toCharArray();
	clauseChoices.put(clauseIndex, new ArrayList<Integer> ());
	final List<Integer> choiceIndices = clauseChoices.get(clauseIndex);
	for (int i  = 0; i < clauseArray.length; ++i) {
		char curChar = clauseArray[i];
		int val = 0;
		if (prevMinus || curChar != '-') {
			val = curChar - '0';
			int indx = val - 1;
			if (choiceIndices.contains(indx)) {
				throw new Error("Contains both a and ~a or a multiple times");
			}
			choiceIndices.add(indx);
			if (!prevMinus) {
				clearDoubleBit (watchList[clauseIndex], indx);
			} else {
				setDoubleBit (watchList[clauseIndex], indx);
			}
		} else if (!prevMinus && curChar == '-') {
			prevMinus = true;
			continue;
		} else {
			throw new Error("Mal-formed input");
		}
	}
}


}

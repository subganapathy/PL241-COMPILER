package registerAlloc;
import intermediateObjects.InterRep.*;
import java.util.*;

import com.sun.org.apache.bcel.internal.generic.NEW;
import com.sun.xml.internal.ws.util.StringUtils;
import cfg.cfg.CFGBlock;

public class RegisterAllocator{
	public class Range{
		private Integer from;
		private Integer to;
		public Integer getFrom() {
			return from;
		}
		public void setFrom(Integer from) {
			this.from = from;
		}
		public Integer getTo() {
			return to;
		}
		public void setTo(Integer to) {
			this.to = to;
		}
		public void SetRange(Integer from, Integer to){
			this.from = from;
			this.to = to;
		}
		public Range(Integer fromRange, Integer toRange){
			from = fromRange;
			to = toRange;
		}
		public Range(){
			
		}
		public Boolean IsCovered(Integer position){
			if(from <= position && to >= position){
				return true;
			}
			return false;
		}
		public Boolean IsTheRangeIntersect(Integer fromLocation, Integer toLocation){
			Boolean returnValue = false;
			if(fromLocation <= from && toLocation >= from){
				returnValue = true;
			}else if(fromLocation <=to && toLocation >=to){
				returnValue = true;
			}else if(fromLocation >=from && toLocation <=to ){
				returnValue = true;
			}
			return returnValue;
		}
	}
	
	public class RangeWithRegister extends Range{
		private String registerAssigned = null;

		public String getRegisterAssigned() {
			return registerAssigned;
		}

		public void setRegisterAssigned(String registerAssigned) {
			this.registerAssigned = registerAssigned;
		}
	}
	
	public class UsePosition{
		private Integer position;
		//use_kind denoting whether a register is required at this position or not:
		private Integer useKind;		
		
		public Integer getUseKind() {
			return useKind;
		}
		public void setUseKind(Integer useKind) {
			this.useKind = useKind;
		}
		public Integer getPosition() {
			return position;
		}
		public void setPosition(Integer position) {
			this.position = position;
		}
		public UsePosition(Integer pos){
			this.position = pos;
		}
	}
	
	public class Interval{
		private String virtualRegister = null;
		private Integer registerAssigned = -1;
		private Integer spillSlotAssigned = -1;
		private ArrayList<UsePosition> usePositions = new ArrayList<UsePosition>();
		private ArrayList<Range> ranges = new ArrayList<Range>();
		private Interval splitParent = null;
		private ArrayList<Interval> splitChild = null;
		private Boolean isSpillSlot = false;
		private Integer spilledAtThisPositionExactly = Integer.MIN_VALUE;
		
		
		public Integer getSpilledAtThisPositionExactly() {
			return spilledAtThisPositionExactly;
		}

		public void setSpilledAtThisPositionExactly(Integer spilledAtThisPositionExactly) {
			this.spilledAtThisPositionExactly = spilledAtThisPositionExactly;
		}

		public ArrayList<RangeWithRegister> GetVirtualToRegisterMapping(Integer fromLocation, Integer toLocation){
			ArrayList<RangeWithRegister> returnValue = new ArrayList<RangeWithRegister>();
			
			Range currentRange = new Range(fromLocation, toLocation);
			Boolean isIntersecting = false;
			for(Range eachRange: ranges){
				if(eachRange.IsTheRangeIntersect(fromLocation, toLocation)){
					isIntersecting = true;
					if(eachRange.getTo() < currentRange.getTo()){
						currentRange.setTo(eachRange.getTo());
					}
					if(eachRange.getFrom() > currentRange.getFrom()){
						currentRange.setFrom(eachRange.getFrom());
					}
				}				
			}
			
			if(isIntersecting){
				RangeWithRegister temp = new RangeWithRegister();
				temp.SetRange(currentRange.getFrom(), currentRange.getTo());
				temp.setRegisterAssigned(GetRegLocation());				
				returnValue.add(temp);
			}
			
			if(splitChild != null){
				for(Interval eachChildInterval: splitChild){
					returnValue.addAll(eachChildInterval.GetVirtualToRegisterMapping(fromLocation, toLocation));			
				}
			}
			
			
			return returnValue;			
		}
		
		private String GetRegLocation(){
			String returnValue = null;
			if(isSpillSlot){
				returnValue = "S"+ spillSlotAssigned;
			}else{
				returnValue = "R"+ registerAssigned;
			}
			return returnValue;
		}
		public String GetLocationofVirtualRegAtPosition(Integer position){
			String returnValue = null;
			
			for(Range eachRanges: ranges){
				if(eachRanges.IsCovered(position)){
					if(isSpillSlot){
						returnValue = "S"+ spillSlotAssigned;
					}else{
						returnValue = "R"+ registerAssigned;
					}
					break;
				}
			}
			
			if(returnValue == null && splitChild != null){
				for(Interval eachChild: splitChild){
					returnValue = eachChild.GetLocationofVirtualRegAtPosition(position);
					if(returnValue != null){
						break;
					}
				}
			}
			
			return returnValue;
		}
		
		public Boolean variableStartsAtSuccessor(Integer successorStartPosition){
			Boolean returnValue = false;
			
			for(Range eachRanges: ranges){
				if(eachRanges.IsCovered(successorStartPosition)){
					returnValue = true;
					break;
				}
			}
			
			if(!returnValue && splitChild != null){
				for(Interval eachChild: splitChild){
					returnValue = eachChild.variableStartsAtSuccessor(successorStartPosition);
					if(returnValue){
						break;
					}
				}
			}
			
			return returnValue;
		}
		public Integer getSpillSlotAssigned() {
			return spillSlotAssigned;
		}
		public void setSpillSlotAssigned(Integer spillSlotAssigned) {
			this.spillSlotAssigned = spillSlotAssigned;
		}
		public Boolean getIsSpillSlot() {
			return isSpillSlot;
		}
		public void setIsSpillSlot(Boolean isSpillSlot) {
			this.isSpillSlot = isSpillSlot;
		}
		public void PrintInterval(){
			System.out.println("");
			System.out.println("Register: " +virtualRegister );
			System.out.println("Range");
			for(Range eachRange: ranges){
				System.out.println("From: "+ eachRange.getFrom() +" TO: " + eachRange.getTo());						
			}
			System.out.println("UsePos");
			for(UsePosition eachPosition:usePositions ){
				System.out.println("Position: "+ eachPosition.getPosition());
				
			}
			System.out.println("");
//			System.out.println("RegisterAssigned:"+ registerAssigned);
//			
//			if(splitChild !=null){
//				for(Interval eachChild: splitChild){
//					eachChild.PrintInterval();
//				}
//			}
		}
		
		public void Print(){
			System.out.println("");
			System.out.println("Register: " +virtualRegister );
			System.out.println("Range");
			for(Range eachRange: ranges){
				System.out.println("From: "+ eachRange.getFrom() +" TO: " + eachRange.getTo());						
			}
			System.out.println("UsePos");
			for(UsePosition eachPosition:usePositions ){
				System.out.println("Position: "+ eachPosition.getPosition());
				
			}
			System.out.println("");
			if(isSpillSlot){
				System.out.println("SpillSlotAssigned:"+ spillSlotAssigned);
			}else{
				System.out.println("RegisterAssigned:"+ registerAssigned);
			}
			if(splitChild !=null){
				for(Interval eachChild: splitChild){
					eachChild.Print();
				}
			}
		}
		
		public void SetFirstRangeFrom(Integer firstFrom){
			if(ranges.size()>0 && ranges.get(0).getTo() >= firstFrom){
				ranges.get(0).setFrom(firstFrom);
			}
		}
		
		public void SetLastRangeTo(Integer lastTo){
			if(ranges.size()>0 && ranges.get(ranges.size()-1).getFrom() <= lastTo){
				ranges.get(ranges.size()-1).setTo(lastTo);
			}
		}
		public Interval getSplitParent() {
			return splitParent;
		}
		public void setSplitParent(Interval splitParent) {
			this.splitParent = splitParent;
		}
		public ArrayList<Interval> getSplitChild() {
			return splitChild;
		}
		public void AddSplitChild(Interval sChild) {
			if(splitChild == null){
				splitChild = new ArrayList<Interval>();
				splitChild.add(sChild);
			}else{
				if(!splitChild.contains(sChild)){
					splitChild.add(sChild);
				}
			}			
		}
		public String getVirtualRegister() {
			return virtualRegister;
		}
		public void setVirtualRegister(String virtualRegister) {
			this.virtualRegister = virtualRegister;
		}
		public void AddUse(Integer currentUsePosition){
			Boolean isInserted = false;
			for(int index =0; index < usePositions.size();index++){
				UsePosition eachPos = usePositions.get(index);
				if(eachPos.position > currentUsePosition){
					isInserted = true;
					usePositions.add(index, new UsePosition(currentUsePosition));
					break;
				}
			}
			if(!isInserted){
				usePositions.add(new UsePosition(currentUsePosition));
			}
		}
//		public void AddUseList(List<UsePosition> tempUsePosition){
//			for(UsePosition eachUse: tempUsePosition){
//				if(!usePositions.contains(eachUse)){
//					usePositions.add(eachUse);
//				}
//			}
//		}
		public Integer getRegisterAssigned() {
			return registerAssigned;
		}
		public void setRegisterAssigned(Integer registerAssigned) {
			this.registerAssigned = registerAssigned;
		}
		public ArrayList<UsePosition> getUsePositions() {
			return usePositions;
		}
		public void setUsePositions(ArrayList<UsePosition> usePositions) {
			this.usePositions = usePositions;
		}
		public void AddRange(Integer from, Integer to){
			Boolean updated = false;
			for(int index =0; index <ranges.size(); index ++ ){
				if(from >= ranges.get(index).getFrom() && (from-2) <= ranges.get(index).getTo()){
					updated = true;
					if(to >= ranges.get(index).getTo()){
						ranges.get(index).setTo(to);
						if((index+1)<ranges.size()){
							if((ranges.get(index).getTo()+2)==ranges.get(index+1).getFrom()){
								ranges.get(index).setTo(ranges.get(index+1).getTo());
								ranges.remove(index+1);
							}
						}
					}
					break;
				}else if((to+2) >= ranges.get(index).getFrom() && to <= ranges.get(index).getTo()){
					updated = true;
					if(from <= ranges.get(index).getFrom()){
						ranges.get(index).setFrom(from);
						if((index-1)>=0){
							if((ranges.get(index).getFrom()-2)==ranges.get(index-1).getTo()){
								ranges.get(index).setFrom(ranges.get(index-1).getFrom());
								ranges.remove(index-1);
							}
						}
					}
					break;
				}
			}
			
			if(!updated){
				for(int index =0; index <ranges.size(); index ++ ){
					if(from < ranges.get(index).getFrom()){
						ranges.add(index, new Range(from, to));
						updated = true;
						break;
					}
				}
			}			
			if(!updated){
				ranges.add(new Range(from, to));
			}
		}
		public void setRanges(ArrayList<Range> ranges) {
			this.ranges = ranges;
		}
		
		public Interval(String vr){
			virtualRegister = vr;
		}
		
		public Integer GetFirstRangeFrom(){
			return ranges.get(0).getFrom();
		}
		public Integer GetLastRangeTo(){
			return ranges.get(ranges.size()-1).getTo();
		}
		public Boolean IsPositionCoveredInInterval(Integer position){
			Boolean returnValue = false;
			for(Range eachRange: ranges){
				if(eachRange.IsCovered(position)){
					returnValue = true;
					break;
				}
			}
			return returnValue;
		}		
		public Integer NextIntersectingLocation(Interval currentInterval){
			Integer returnValue = -1;
			Integer currentLocation = currentInterval.GetFirstRangeFrom();
			int index = 0;
			for(; index < ranges.size() ; index ++){
				if(ranges.get(index).getFrom() > currentLocation){
					returnValue = ranges.get(index).getFrom();
					return returnValue;
				}
			}
			return returnValue;
		}
		public void SplitBeforeUsePosition(Integer usePos){
			Split(false, -1, usePos-2);
		}
		public void SplitAtPosition(Integer nextSpillSlot, Integer pos){
			Split(true, nextSpillSlot , pos);
		}
		public void SplitAtEndOfLifeTimeHole(Integer nextSpillSlot, Integer currentPos){
			int index = 0;
			for(; index < ranges.size() ; index ++){
				if(ranges.get(index).getFrom() >= currentPos &&
						ranges.get(index).getTo() <= currentPos){
					if(index < ranges.size()-1){
						Split(true, nextSpillSlot,  ranges.get(index).getFrom());
					}
					break;
				}
			}
			
		}
		public void SpiltAtOptimalPosition(Integer regFreePos){
			Integer optimalPosition = FindOptimalPosition(regFreePos);
			Split(false, -1 , optimalPosition);
		}
		private void Split(Boolean spill, Integer nextSpillSlot, Integer optimalPosition){
					
			if(virtualRegister.compareTo("Akt_2")==0){
				System.out.println();
			}
			if(ranges.get(0).getFrom() == optimalPosition){
				isSpillSlot = true;
				spillSlotAssigned = nextSpillSlot;
				registerAssigned =-1;
				RemoveFromActiveOrInActiveInterval(this);
				return;
				//remove from active
			}
			Interval newSplitInterval = new Interval(virtualRegister);
			int index = 0;
			int temp = Integer.MAX_VALUE;
			for(; index < ranges.size(); index ++){
				if(ranges.get(index).getFrom() < optimalPosition){
					Integer splitIntervalFirstTo = ranges.get(index).getTo();
					if(splitIntervalFirstTo > optimalPosition){
						ranges.get(index).setTo(optimalPosition);
						newSplitInterval.AddRange(optimalPosition, splitIntervalFirstTo);
						if(temp == Integer.MAX_VALUE){
							temp = index;
						}
					}
				}else
				{
					if(temp == Integer.MAX_VALUE){
						temp = index;
					}
					newSplitInterval.AddRange(ranges.get(index).getFrom(), ranges.get(index).getTo());
				}
			}
			
			if(temp != Integer.MAX_VALUE){								
				Integer rangeSize = ranges.size();
				if(temp != (rangeSize-1)){
					if( 0 == temp ){
						ranges.clear();
					}
					else{
						List<Range> deletelist = ranges.subList(temp , rangeSize-1);
						ranges.removeAll(deletelist);
					}					
				}
				
				if(spill == true){
					Interval newSpillInterval = new Interval(virtualRegister);
					Integer lastUsePosition = 0;
					for(int i=0 ; i< usePositions.size();i++){
						if(usePositions.get(i).position <= optimalPosition){
							lastUsePosition = usePositions.get(i).position;
						}
					}
					
					if(lastUsePosition ==0){
						isSpillSlot = true;
						spillSlotAssigned = nextSpillSlot;
						registerAssigned =-1;
						RemoveFromActiveOrInActiveInterval(this);
						return;
					}else{
						Range newRange = new Range();
						newRange.setFrom(lastUsePosition+2);
						newRange.setTo(ranges.get(ranges.size()-1).getTo());
						newSpillInterval.ranges.add(newRange);				
						int k = ranges.size()-1;
						for(;k>=0;k--){
							if(ranges.get(k).getFrom()<=lastUsePosition){
								ranges.get(k).setTo(lastUsePosition+2);
								break;
							}else{
								ranges.remove(k);
							}
						}
						
						
						if(this.splitParent == null){
							newSpillInterval.setSplitParent(this);
						}else{
							newSpillInterval.setSplitParent(this.splitParent);
						}
						newSpillInterval.isSpillSlot = true;
						newSpillInterval.spillSlotAssigned = nextSpillSlot;
						newSpillInterval.registerAssigned =-1;
						newSpillInterval.getSplitParent().AddSplitChild(newSpillInterval);
					}
				}
				//Update use positions
				for(index =0; index < usePositions.size();){
					if(usePositions.get(index).getPosition() >= optimalPosition){
						newSplitInterval.AddUse(usePositions.get(index).getPosition());
						usePositions.remove(index);
					}else{
						index++;
					}
				}				
				if(newSplitInterval.usePositions.size() !=0){
				//assigning parent
					if(this.splitParent == null){
						newSplitInterval.setSplitParent(this);
					}else{
						newSplitInterval.setSplitParent(this.splitParent);
					}
					
					
					AddNewIntervelToUnHandledList(newSplitInterval);
					//newSplitInterval.ranges.get(0).setFrom(newSplitInterval.ranges.get(0).getFrom()+2);
					newSplitInterval.getSplitParent().AddSplitChild(newSplitInterval);
				}
				
				
				
			}else{
				//ERROR
				System.out.println("ERROR- Split(Integer optimalPosition)");
			}			
		}
		
		
		private void RemoveFromActiveOrInActiveInterval(Interval newInterval)
		{
			if(activeIntervals.contains(newInterval)){
				int index = activeIntervals.indexOf(newInterval);
				activeIntervals.remove(index);
				handledIntervals.add(newInterval);
			}
			
			if(inactiveIntervals.contains(newInterval)){
				int index = inactiveIntervals.indexOf(newInterval);
				inactiveIntervals.remove(index);
				handledIntervals.add(newInterval);
			}
		}
		private void AddNewIntervelToUnHandledList(Interval newSplitInterval){
			Boolean isAdded = false;
			for(int index = 0; index < unhandledIntervals.size(); index ++){
				if(unhandledIntervals.get(index).GetFirstRangeFrom() >= newSplitInterval.GetFirstRangeFrom()){
					unhandledIntervals.add(index, newSplitInterval);
					isAdded = true;
					break;
				}
			}
			if(!isAdded){
				unhandledIntervals.add(newSplitInterval);
			}
		}		
		private Integer FindOptimalPosition(Integer regFreePos){
			Integer returnValue = regFreePos;
			//TODO: find optimal value and Move operation b/w two interval is inserted at split position						
			return returnValue;
		}
		public Integer NextUsePosition(Integer currentPosition){
			Integer returnValue = 0;
			for(UsePosition eachUsePosition: usePositions){
				if(eachUsePosition.getPosition() > currentPosition){
					returnValue = eachUsePosition.getPosition();
					break;
				}
			}
			return returnValue;
		}
		public Integer GetFirstUsePosition(){
			Integer returnValue = -1;
			if(usePositions.size() > 0){
				returnValue = usePositions.get(0).getPosition();
			}
			return returnValue;
		}
	}
	
	private ArrayList<Interval> unhandledIntervals = new ArrayList<Interval>();
	private ArrayList<Interval> handledIntervals = new ArrayList<Interval>();
	private ArrayList<Interval> activeIntervals = new ArrayList<Interval>();
	private ArrayList<Interval> inactiveIntervals = new ArrayList<Interval>();
	private Interval currentInterval = null;
	private Integer[] registerFreeLocation = new Integer[8];
	private Integer[] registerUsePosition = new Integer[8];
	private ArrayList<Integer> freeSpillSlots = new ArrayList<Integer>();
	private Integer nextSpillSlot = 0;
	
	//Register Allocation
	protected ArrayList< CFGBlock > dfsPostOrderVertex = new ArrayList<CFGBlock>();
	private ArrayList< CFGBlock> tempdfsVertex = new ArrayList<CFGBlock> ();
	private HashMap<String, Interval> variableRange = new HashMap<String, Interval>();
	private HashMap<String, FrameInfo> sSAnameVsFrameInfo = new HashMap<String, FrameInfo>();
	private Boolean registerAssigned = false;
	
	private ArrayList<CFGBlock> reverseLoopCheck = new ArrayList<CFGBlock>();
	
	//Register Allocation
	private void DfsPostOrderTraversal(CFGBlock current){
		ArrayList< CFGBlock> workList = new ArrayList<CFGBlock>();
		//Worklist - add root
		workList.add(current);
		
		while(!workList.isEmpty()){
			CFGBlock firstCFGBlock = workList.remove(0);
			
			for(CFGBlock eachPredessorBlock: firstCFGBlock.PredecessorList()){
				if(eachPredessorBlock.BlockLabel().compareTo("ROOT") != 0){
					String[] eachBlockSplit = eachPredessorBlock.BlockLabel().split(":");
					Integer eachBlockNumber = Integer.parseInt(eachBlockSplit[eachBlockSplit.length -1]);
					String[] currentBlockSplit = firstCFGBlock.BlockLabel().split(":");
					Integer currentBlockNumber = Integer.parseInt(currentBlockSplit[currentBlockSplit.length -1]);
					
					//Avoid Backward edge
					if(eachBlockNumber < currentBlockNumber){
						if(!tempdfsVertex.contains(eachPredessorBlock)){
							continue;
						}
					}
				}
			}
			
			System.out.println("temp Block add"+ firstCFGBlock.BlockLabel());
			tempdfsVertex.add(firstCFGBlock);
			
			ArrayList<CFGBlock> successWithoutBackLoop = new ArrayList<CFGBlock>();
			for(CFGBlock eachBlock: firstCFGBlock.SuccessorList()){
				if(!workList.contains(eachBlock)){
					if(tempdfsVertex.contains(eachBlock)){
						eachBlock.setIsLoopStartingBlock(true);
						firstCFGBlock.setLoopStartingBlock(eachBlock);
					}else
					{
						successWithoutBackLoop.add(eachBlock);
					}
				}
			}
			
			if(!successWithoutBackLoop.isEmpty()){
				//Sort and add to list

				for(CFGBlock eachBlock: successWithoutBackLoop){
					int sizeBefore = workList.size();
					for(int index = 0; index < workList.size(); index++){
						String[] eachBlockSplit = eachBlock.BlockLabel().split(":");
						Integer eachBlockNumber = Integer.parseInt(eachBlockSplit[eachBlockSplit.length -1]);
						String[] currentBlockSplit = workList.get(index).BlockLabel().split(":");
						Integer currentBlockNumber = Integer.parseInt(currentBlockSplit[currentBlockSplit.length -1]);
						if(eachBlockNumber <= currentBlockNumber){
							workList.add(index, eachBlock);
							break;
						}
					}
					
					if(sizeBefore == workList.size()){
						workList.add(eachBlock);
					}
				}
			}
		}
		
		
//		if(!tempdfsVertex.contains(current)){
//			tempdfsVertex.add(current);
//		}
//		reverseLoopCheck.add(current);
//		ArrayList<CFGBlock> successorList = current.SuccessorList();
//		for(int index = 0; index < successorList.size() ; index++){
//			CFGBlock eachBlock = successorList.get(index);
//			if(!reverseLoopCheck.contains(eachBlock)){
//				DfsPostOrderTraversal(eachBlock);
//			}else{
//				//eachBlock - Loop Starting
//				//current - one if loop ending
//				//WhileLoopEnding block
//				current.setLoopStartingBlock(eachBlock);
//				eachBlock.setIsLoopStartingBlock(true);
//			}
//		}
//		reverseLoopCheck.remove(current);
	}
	
	private void UpdateNumbering(){
		int fromNumber = 2;
		int loopcounter = dfsPostOrderVertex.size() -1;
		for(int i= loopcounter ; i>=0;i--){
			CFGBlock block = dfsPostOrderVertex.get(i);
			int totalElements = block.getSizeOfPhiAndStatement();
			if(totalElements==0){
				block.setFromLocation(fromNumber-2);
				block.setToLocation(fromNumber-2);
			}else{
				block.setFromLocation(fromNumber);
				block.setToLocation(fromNumber + 2 *(totalElements - 1));
				block.AddMapping();
				fromNumber += 2* totalElements;
			}
			//Update While LoopEndLocation
			if(block.getLoopStartingBlock() != null){
				if(block.getLoopStartingBlock().getLoopEndingLocation() < block.getToLocation()){
					block.getLoopStartingBlock().setLoopEndingLocation(block.getToLocation());
				}
			}
		}
	}
	
	private void BuildIntervals(){
		
		for(int index = 0; index < dfsPostOrderVertex.size(); index++){
			CFGBlock eachCFGBlock = dfsPostOrderVertex.get(index);
			ArrayList<String> live = new ArrayList<String>();
			
			//Get all live range from successor
			for(CFGBlock successorBlock : eachCFGBlock.SuccessorList()){
				ArrayList<String> successorLive = successorBlock.getLiveIn();
				for(String eachSuccessorLive: successorLive){
					if(!live.contains(eachSuccessorLive)){
						live.add(eachSuccessorLive);
					}
				}
			}

			Integer lastPhiStatementNumber =0;
			for(CFGBlock successorBlock : eachCFGBlock.SuccessorList()){
				ArrayList<FrameInfo> successorLive = successorBlock.PhiInputOfCFGBlock(eachCFGBlock);
				if(lastPhiStatementNumber < successorBlock.GetLastPhiFunctionNumber()){
					lastPhiStatementNumber = successorBlock.GetLastPhiFunctionNumber();
				}
				for(int i =0; i < successorLive.size(); i ++){

					FrameInfo eachSuccessorLive = successorLive.get(i);
					if(!live.contains(eachSuccessorLive.serializeMe())){
						live.add(eachSuccessorLive.serializeMe());
						AddVariableRange(eachSuccessorLive.serializeMe(), successorBlock.getFromLocation(), successorBlock.getFromLocation()+ (i+1)*2);
						variableRange.get(eachSuccessorLive.serializeMe()).AddUse(successorBlock.getFromLocation()+ (i)*2);
						sSAnameVsFrameInfo.put(eachSuccessorLive.serializeMe(), eachSuccessorLive);
					}
				}			
			}
			
			for(String eachLive: live){
				AddVariableRange(eachLive, eachCFGBlock.getFromLocation(), eachCFGBlock.getToLocation());
			}
			
			int statmentCount = eachCFGBlock.GetStatementsList().size()-1;
			for(int i = statmentCount; i>=0; i--){
				CodeBlock cb = eachCFGBlock.GetStatementsList().get(i);
				if(!cb.isDeleted /*&& !cb.isCall*/){
					//Output operands
					Integer operationId = eachCFGBlock.GetVirtualNumberForLabelValue(cb.label);
					if((!cb.isArgPassingStatement) &&
							cb.outputTemporary.serializeMe() != null &&
							cb.outputTemporary.serializeMe().length() > 0 &&
							!intermediateObjects.InterRep.globalSymTab.isGlobal(cb.outputTemporary.tempID) &&
							variableRange.containsKey(cb.outputTemporary.serializeMe())){
						
						
						if(operationId>0)
						{
							variableRange.get(cb.outputTemporary.serializeMe()).SetFirstRangeFrom(operationId);
							variableRange.get(cb.outputTemporary.serializeMe()).AddUse(operationId);
						}
						if(live.contains(cb.outputTemporary.serializeMe()))
						{
							live.remove(cb.outputTemporary.serializeMe());
						}else{
							AddVariableRange(cb.outputTemporary.serializeMe(), operationId, operationId+2 );
							sSAnameVsFrameInfo.put(cb.outputTemporary.serializeMe(), cb.outputTemporary);
						}
					}
					//Input operands
					if( cb.isCall ) continue;
					int operSize = cb.operands.size();
					for(int j =0 ;j< operSize; j++){
						FrameInfo eachFrameInfo = cb.operands.get(j);
						if(eachFrameInfo instanceof LocationInfo && 
								!intermediateObjects.InterRep.globalSymTab.isGlobal(eachFrameInfo.tempID)){
							if(eachFrameInfo.serializeMe().contains("RETURN")){
								continue;
							}
							Integer tempOper = operationId;
							if(cb.opCode >= CodeBlock.kBNE && cb.opCode <= CodeBlock.kBGT && j==0){
								if(lastPhiStatementNumber !=0 && lastPhiStatementNumber>= eachCFGBlock.getFromLocation()){
									operationId = lastPhiStatementNumber;
								}
							}
							AddVariableRange(eachFrameInfo.serializeMe(), eachCFGBlock.getFromLocation(),
									operationId);
							sSAnameVsFrameInfo.put(eachFrameInfo.serializeMe(), eachFrameInfo);
							variableRange.get(eachFrameInfo.serializeMe()).AddUse(tempOper);
							if(!live.contains(eachFrameInfo.serializeMe())){
								live.add(eachFrameInfo.serializeMe());
							}
						}
					}
				}
			}
			
			int j=0;
			for(CodeBlock phiCb: eachCFGBlock.returnPhiFunctions().values()){
				if(!phiCb.isDeleted){
					sSAnameVsFrameInfo.put(phiCb.outputTemporary.tempID, phiCb.outputTemporary);
					if(live.contains(phiCb.outputTemporary.serializeMe())){
						live.remove(phiCb.outputTemporary.serializeMe());
					}else{
						if(!intermediateObjects.InterRep.globalSymTab.isGlobal(phiCb.outputTemporary.tempID)){
							AddVariableRange(phiCb.outputTemporary.serializeMe(), eachCFGBlock.getFromLocation(), eachCFGBlock.getFromLocation()+ (j+1)*2 );
							variableRange.get(phiCb.outputTemporary.serializeMe()).AddUse(eachCFGBlock.getFromLocation()+ (j)*2);
						}
					}
					j++;
				}
			}
			
			if(eachCFGBlock.getIsLoopStartingBlock()){
				for(String operands: live){
					AddVariableRange(operands, eachCFGBlock.getFromLocation(), eachCFGBlock.getLoopEndingLocation());
				}
			}			
			eachCFGBlock.setLiveIn(live);
		}
	}
	
	private void AddVariableRange(String eachOpd, Integer from, Integer to)
	{
		if(!variableRange.containsKey(eachOpd)){
			Interval inv = new Interval(eachOpd);
			inv.AddRange(from, to);
			variableRange.put(eachOpd, inv);
		}else{
			variableRange.get(eachOpd).AddRange(from,to);
		}	
	}
	
	private Integer GetRegisterWithHighFreePos(Integer[] registerAttributes){
		Integer returnValue = -1;
		Integer temp = Integer.MIN_VALUE;
		
		for(int index =0; index < registerAttributes.length ; index ++){
			if(registerAttributes[index] >= temp){
				returnValue = index;
				temp = registerAttributes[index];
			}
		}
		return returnValue;
	}
	
	private Boolean TryAllocateFreeReg(){
		Boolean returnValue = true;
		for(int index =0; index < registerFreeLocation.length; index ++){
			registerFreeLocation[index] = Integer.MAX_VALUE;
		}
		
		for(Interval eachActiveInterval: activeIntervals){
			if(eachActiveInterval.getRegisterAssigned() < registerFreeLocation.length &&
					eachActiveInterval.getRegisterAssigned() > -1){
				registerFreeLocation[eachActiveInterval.getRegisterAssigned()] =0;
			}
		}
		
		for(Interval eachInactiveInterval: inactiveIntervals){
			Integer nextPosition = eachInactiveInterval.NextIntersectingLocation(eachInactiveInterval);
			if(nextPosition != -1){
				registerFreeLocation[eachInactiveInterval.getRegisterAssigned()] = nextPosition;
			}
		}
		
		Integer reg = GetRegisterWithHighFreePos(registerFreeLocation);
		
		if(registerFreeLocation[reg] == 0){
			returnValue = false;
		}else if(registerFreeLocation[reg] > currentInterval.GetLastRangeTo()){
			currentInterval.setRegisterAssigned(reg);
			registerAssigned = true;
		}else{
			currentInterval.SpiltAtOptimalPosition(registerFreeLocation[reg]);
			currentInterval.setRegisterAssigned(reg);
			registerAssigned = true;
		}
		
		return returnValue;
	}
	
	private void AllocateBlockedReg(){
		HashMap<Integer, Interval> registerVsInterval = new HashMap<Integer, Interval>();
		for(int index =0; index < registerUsePosition.length; index ++){
			registerUsePosition[index] = Integer.MAX_VALUE;
		}		
		for(Interval eachActiveInterval: activeIntervals){
			registerVsInterval.put(eachActiveInterval.getRegisterAssigned(), eachActiveInterval);
			Integer usePos = eachActiveInterval.NextUsePosition(currentInterval.GetFirstRangeFrom());
			if(registerUsePosition[eachActiveInterval.getRegisterAssigned()] > usePos){
				registerUsePosition[eachActiveInterval.getRegisterAssigned()] = usePos;
			}
		}		
		
		for(Interval eachInactiveInterval: inactiveIntervals){
			registerVsInterval.put(eachInactiveInterval.getRegisterAssigned(), eachInactiveInterval);
			Integer nextPosition = eachInactiveInterval.NextIntersectingLocation(eachInactiveInterval);
			if(nextPosition != -1){
				Integer usePos = eachInactiveInterval.NextUsePosition(currentInterval.GetFirstRangeFrom());
				if(registerUsePosition[eachInactiveInterval.getRegisterAssigned()] > usePos){
					registerUsePosition[eachInactiveInterval.getRegisterAssigned()] = usePos;
				}
			}
		}
			
		//Note: No Fixed registers are used
		Integer reg = GetRegisterWithHighFreePos(registerUsePosition);
		UsePosition firstUsePosition = currentInterval.getUsePositions().get(0);
		if(registerUsePosition[reg] < firstUsePosition.position && registerUsePosition[reg] !=0){
			//assign spill slot to current
			currentInterval.setIsSpillSlot(true);
			currentInterval.setRegisterAssigned(-1);
			if(freeSpillSlots.isEmpty()){
				currentInterval.setSpillSlotAssigned(nextSpillSlot);
				nextSpillSlot+=1;
			}else{
				currentInterval.setSpillSlotAssigned(freeSpillSlots.get(0));
				freeSpillSlots.remove(0);
			}
			currentInterval.SplitBeforeUsePosition(currentInterval.GetFirstUsePosition());
		}else{
			registerAssigned = true;
			currentInterval.setRegisterAssigned(reg);
			if(registerUsePosition[reg] !=0){
				if(activeIntervals.contains(registerVsInterval.get(reg))){
					registerVsInterval.get(reg).SplitAtPosition(nextSpillSlot, registerUsePosition[reg]-2);
					nextSpillSlot+=1;
					//registerVsInterval.get(reg).setSpilledAtThisPositionExactly(currentInterval.GetFirstUsePosition()-2);
				}else if(inactiveIntervals.contains(registerVsInterval.get(reg))){
					registerVsInterval.get(reg).SplitAtEndOfLifeTimeHole(nextSpillSlot, registerUsePosition[reg]);
					nextSpillSlot+=1;
					//registerVsInterval.get(reg).setSpilledAtThisPositionExactly(currentInterval.GetFirstUsePosition()-2);
				}else{
					//Do Nothing
				}
			}
		}
		
		
		// make sure that current does not intersect with
		// the fixed interval for reg
//		if current intersects with the fixed interval for reg then
//		split current before this intersection
		
		
//		If an interval is used in a loop, it should not be spilled because
//		this requires a load and a store in each loop iteration.
//		The spilling heuristic only considers future use positions,
//		but does not look backward to previous uses. To prevent
//		the spilling of intervals that are used in a loop, pseudo use
//		positions are inserted for them at the end of the loop just
//		before the backward branch. So the heuristic prefers to spill
//		intervals that are used after the loop instead of intervals that
//		are used in the loop.
	}	
	private void SortIntervals(){
		for(String eachIntervalKey: variableRange.keySet()){
			Interval intvData = variableRange.get(eachIntervalKey);
			
			int index = 0;
			//finding exact index
			for (Interval unhandledInterval: unhandledIntervals){
				if (unhandledInterval.GetFirstRangeFrom() > intvData.GetFirstRangeFrom())
				{
					break;
				}
				index ++;
			}
			unhandledIntervals.add(index, intvData);
		}
	}
		
	private void LinearScanRegisterAllocation(){
		SortIntervals();
		activeIntervals.clear();
		inactiveIntervals.clear();
		handledIntervals.clear();
		currentInterval = null;
		while(!unhandledIntervals.isEmpty()){
			registerAssigned = false;
			currentInterval = unhandledIntervals.get(0);
			Integer currentPosition = currentInterval.GetFirstRangeFrom();
			Integer index = 0;
					
			if(currentInterval.getVirtualRegister().compareTo("Akt_2")==0){
				System.out.println();
			}

			// check for intervals in active that are handled or inactive
			for(; index < activeIntervals.size();){
				Interval eachActive = activeIntervals.get(index);
				if(eachActive.GetLastRangeTo() < currentPosition){
					activeIntervals.remove(eachActive);
					handledIntervals.add(eachActive);
					if(eachActive.isSpillSlot){
						freeSpillSlots.add(eachActive.getSpillSlotAssigned());
					}
				}else if(!eachActive.IsPositionCoveredInInterval(currentPosition)){
					activeIntervals.remove(eachActive);
					inactiveIntervals.add(eachActive);
				}else{
					index ++;
				}
			}
			
			// check for intervals in inactive that are expired or active
			for(index =0; index<inactiveIntervals.size();){
				Interval eachInactive = inactiveIntervals.get(index);
				if(eachInactive.GetLastRangeTo() < currentPosition){
					inactiveIntervals.remove(eachInactive);
					handledIntervals.add(eachInactive);
					if(eachInactive.isSpillSlot){
						freeSpillSlots.add(eachInactive.getSpillSlotAssigned());
					}
				}else if(eachInactive.IsPositionCoveredInInterval(currentPosition)){
					inactiveIntervals.remove(eachInactive);
					activeIntervals.add(eachInactive);
				}else{
					index++;
				}
			
			}
			
			if(!TryAllocateFreeReg()){
				AllocateBlockedReg();
			}
			
			if(registerAssigned){
				activeIntervals.add(currentInterval);
			}
			unhandledIntervals.remove(currentInterval);
		}
	}
	
	private void ResolutionAndSSADeconstruction(){
		String moveFrom;
		String moveTo;
		String moveFromTempId;
		String moveToTempId;

		
		for(int i=dfsPostOrderVertex.size()-1; i>=0;i--){
			CFGBlock predecessorCB = dfsPostOrderVertex.get(i);
			for(CFGBlock successorCB: predecessorCB.SuccessorList()){
				
				for(String eachPhiKey: successorCB.getPhiFunctions().keySet()){
					FrameInfo operand = successorCB.getPhiFnDefiningVarAndInputOfPred(eachPhiKey, predecessorCB);
					if(!successorCB.getPhiFunctions().get(eachPhiKey).isDeleted 
							&& operand != null ){
						moveFromTempId = operand.tempID;
						if(operand instanceof ConstFrameInfo){
							moveFrom = operand.serializeRA();
						}else{
							
							if(variableRange.containsKey(operand.serializeRA())){
								moveFrom = variableRange.get(operand.serializeRA()).GetLocationofVirtualRegAtPosition(
										predecessorCB.getToLocation());
							}else if(intermediateObjects.InterRep.globalSymTab.isGlobal(operand.tempID)){
								moveFrom = "G"+intermediateObjects.InterRep.globalSymTab.getGlobalRegisterSpillingLoc(operand.tempID);
							}else{
								continue;
							}
						}
						
						FrameInfo outputFrameInfo = successorCB.getPhiFnOutputFrame(eachPhiKey, predecessorCB);
						moveToTempId = outputFrameInfo.tempID;
						if(variableRange.containsKey(outputFrameInfo.serializeRA())){
							moveTo = variableRange.get(outputFrameInfo.serializeRA()).GetLocationofVirtualRegAtPosition(
									successorCB.getFromLocation());
						}else if(intermediateObjects.InterRep.globalSymTab.isGlobal(outputFrameInfo.tempID)){
							moveTo = "G"+intermediateObjects.InterRep.globalSymTab.getGlobalRegisterSpillingLoc(outputFrameInfo.tempID);
						}else{
							continue;
						}
						
						Integer loc;
						if(predecessorCB == null){
							loc = successorCB.getFromLocation();
						}else{
							loc =predecessorCB.getToLocation();
						}
						
						if(moveFrom.compareTo(moveTo) != 0){
							System.out.println("TYPE 1 "+eachPhiKey+"--> Loc:"+loc+" From:"+moveFrom+" To:"+moveTo);
							predecessorCB.AddMoveInstFromRegAlloc(loc, moveFrom, moveTo);
							predecessorCB.putTempIdFix(moveFrom, loc, moveFromTempId);
							predecessorCB.putTempIdFix(moveTo, loc, moveToTempId);
						}
					}
				}
				
				for(String eachLiveInVariable: successorCB.getLiveIn()){
					moveFrom = null;
					moveTo = null;
					moveFromTempId = null;
					moveToTempId = null;
					Interval liveInInterval = variableRange.get(eachLiveInVariable);
										
					moveFrom = liveInInterval.GetLocationofVirtualRegAtPosition(predecessorCB.getToLocation());
					moveTo = liveInInterval.GetLocationofVirtualRegAtPosition(successorCB.getFromLocation());
					if(moveFrom!=null && moveTo!=null && moveFrom.compareTo(moveTo) != 0){
						System.out.println("TYPE 2 "+liveInInterval.getVirtualRegister()+"--> Loc:"+predecessorCB.getToLocation()+" From:"+moveFrom+" To:"+moveTo);
//						moveFromTempId = sSAnameVsFrameInfo.get(moveFrom).tempID;
//						moveToTempId = sSAnameVsFrameInfo.get(moveTo).tempID;
						predecessorCB.AddMoveInstFromRegAlloc(predecessorCB.getToLocation(), moveFrom, moveTo);
						predecessorCB.putTempIdFix(moveFrom, predecessorCB.getToLocation(), sSAnameVsFrameInfo.get(liveInInterval.virtualRegister).tempID);
						predecessorCB.putTempIdFix(moveTo, predecessorCB.getToLocation(), sSAnameVsFrameInfo.get(liveInInterval.virtualRegister).tempID);
					}
				}
			}
			
			for(Interval liveInInterval: unhandledIntervals){
				if(liveInInterval.GetFirstRangeFrom()<predecessorCB.getToLocation()){
					ArrayList<RangeWithRegister> mapping = liveInInterval.GetVirtualToRegisterMapping(predecessorCB.getFromLocation(),
							predecessorCB.getToLocation());
					HashMap<Range, String> mappingInHash = new HashMap<Range, String>();
					
					for(RangeWithRegister each: mapping){
						mappingInHash.put((Range)each, each.getRegisterAssigned());
					}
					
					predecessorCB.AddMappingOfVirtualToActualRegister(liveInInterval.getVirtualRegister(), mappingInHash);
					
					String previousPos = null;
					Integer previous = Integer.MIN_VALUE;
					Integer current = Integer.MIN_VALUE;
					for(RangeWithRegister eachRange: mapping){
						String currentLoc = eachRange.getRegisterAssigned();
						//System.out.println(liveInInterval.getVirtualRegister()+"--> Loc:"+eachRange.getFrom()+" From:"+previousPos+" To:"+currentLoc);
						if(eachRange.getFrom() ==eachRange.getTo()){
							continue;
						}				
						current = eachRange.getTo();
						if(previousPos == null){
							previousPos = currentLoc;
							previous = current;
							continue;
						}
						
						if(previousPos.compareTo(currentLoc)!=0 && previous != Integer.MIN_VALUE){
							System.out.println("TYPE 3 "+liveInInterval.getVirtualRegister()+"--> Loc:"+eachRange.getFrom()+" From:"+previousPos+" To:"+currentLoc);
							predecessorCB.AddMoveInstFromRegAlloc(previous, previousPos, currentLoc);
							predecessorCB.putTempIdFix(previousPos, eachRange.getFrom(), sSAnameVsFrameInfo.get(liveInInterval.virtualRegister).tempID);
							predecessorCB.putTempIdFix(currentLoc, eachRange.getFrom(), sSAnameVsFrameInfo.get(liveInInterval.virtualRegister).tempID);
						}
						previous = current;
						previousPos = currentLoc;
					}
				}
			}			
			predecessorCB.OrderAndInsertMoves();
		}
		
		for(int i=0; i<dfsPostOrderVertex.size();i++){
			dfsPostOrderVertex.get(i).DeleteAllPhiBlock();
		}
		
	}
	
	private void FixUpForSplitIntermediateFix(){
		
		
		for(Interval eachInterval: unhandledIntervals){
			if(eachInterval.getVirtualRegister().compareTo("foo:1")==0){
				System.out.print("");
			}
			if(eachInterval.getSpilledAtThisPositionExactly()!= Integer.MIN_VALUE &&
					eachInterval.getSplitChild() != null && 
					eachInterval.getSplitChild().size()>0){
				eachInterval.SetLastRangeTo(eachInterval.getSpilledAtThisPositionExactly());
				eachInterval.getSplitChild().get(0).SetFirstRangeFrom(eachInterval.getSpilledAtThisPositionExactly()+2);
			}
			
			if(eachInterval.getSplitChild() != null){
				for(int index =0 ; index < eachInterval.getSplitChild().size(); index++){
					Interval child = eachInterval.getSplitChild().get(index);
					
					if(child.getSpilledAtThisPositionExactly()!= Integer.MIN_VALUE &&
							(index+1)< eachInterval.getSplitChild().size()){
						child.SetLastRangeTo(eachInterval.getSpilledAtThisPositionExactly());
						eachInterval.getSplitChild().get(index+1).SetFirstRangeFrom(eachInterval.getSpilledAtThisPositionExactly()+2);
					}
				}
			}
		}
		
	
	}
	
	//TODO:Fixed registers
	public void BuildRegAllocUsingLinearScan(CFGBlock rootNode){
		DfsPostOrderTraversal(rootNode);
		
		if(tempdfsVertex != null){
			for(int index = tempdfsVertex.size()-1;index >=0 ; index --){
				dfsPostOrderVertex.add(tempdfsVertex.get(index));
			}
		}
		
		//print
		for(CFGBlock eBlock: dfsPostOrderVertex){			
			if(eBlock.getLoopStartingBlock() !=null){
				CFGBlock startingBlock = eBlock.getLoopStartingBlock();
				if(startingBlock.getIsLoopStartingBlock()){
					System.out.println(eBlock.BlockLabel()+"--> Starting Loop at "+ startingBlock.BlockLabel()+"--"+eBlock.getIsLoopStartingBlock());
				}
			}else{
				System.out.println(eBlock.BlockLabel()+"--"+eBlock.getIsLoopStartingBlock());
			}
		}
		
		UpdateNumbering();
		BuildIntervals();
		for(Interval eachInterval: variableRange.values()){
			eachInterval.PrintInterval();
		}
		LinearScanRegisterAllocation();
		unhandledIntervals.clear();
		SortIntervals();
		//FixUpForSplitIntermediateFix();
		System.out.println("");
		System.out.println("After register Allocation");
	
		System.out.println("");
		for(Interval eachInterval: variableRange.values()){
			eachInterval.Print();
		}
		ResolutionAndSSADeconstruction();
	}
}

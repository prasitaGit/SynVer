from openai import OpenAI
import subprocess
import json
import pdb
import os
import time
import sys


#string representation of a goal
def getStringRepresentation(goalComponents):
  goalOp = ''
  for hhypo in goalComponents['hypotheses']:
    strNames = ",".join(hhypo['names'])+": "+hhypo["type"]+"\n"
    goalOp = goalOp + strNames
    goalOp = goalOp + "\n-------------------------------------------------------------------------------------------------------------------------------\n"
    goalOp = goalOp + goalComponents['conclusion']
  return goalOp


def stringErrorRepOfTactics(cg):
  if len(goal_errtac[cg]) == 0:
    return ''
  errStr = '['
  errTac = goal_errtac[cg]
  for tac in errTac:
     errStr = errStr + tac + ','
  #exclude last comma
  errStr = errStr[:-1] + ']'
  return errStr

def countConclusion(cg):
  #json load..
  cgJson = json.loads(cg)
  return len(cgJson["conclusion"])

def deepCompare(gpar, gchild): #returns true if parent and child contents are same. False, otherwise.
  #gpar = json.loads(g1)
  #gchild = json.loads(g2)
  if "goals"  not in gpar or "goals" not in gchild: 
    return True
  elif len(gpar["goals"]) != len(gchild["goals"]):
    #not same
    return False
  elif len(gpar["goals"]) == 0:
    return True
  else: #lengths are same and non-zero
    lenGoals = len(gpar["goals"])
    for ind in range(lenGoals):
      #json objects
      goalPar = gpar["goals"][ind]
      goalChild = gchild["goals"][ind]
      if goalPar["conclusion"] != goalChild["conclusion"]:
        return False #not same
      else:
        #loop through hypothesis
        listhypoPar = goalPar["hypotheses"]
        listhypoChild = goalChild["hypotheses"]
        if len(listhypoPar) != len(listhypoChild):
          #not the same
          return False
        else: #lengths of hypothesis also same. Capture types.
          lenHypotheses = len(listhypoPar)
          listParHypoTypes = []
          listChildHypoTypes = []
          for indh in range(lenHypotheses):
            hypoPar = goalPar["hypotheses"][indh]
            hypoChild = goalChild["hypotheses"][indh]
            #appended
            listParHypoTypes.append(hypoPar["type"])
            listChildHypoTypes.append(hypoChild["type"])
          if sorted(listParHypoTypes) != sorted(listChildHypoTypes):
            return False #not same, content wise
    return True

         

def insert_before_last_line(file_path, tactic):
    with open(file_path, 'r') as f:
        lines = f.readlines()
  
    lines = lines[:-1] + [tactic+'\n'] + [lines[-1]]

    with open(file_path, 'w') as f:
        f.writelines(lines)

def delete_second_last_line(file_path):
    with open(file_path, 'r') as f:
        lines = f.readlines()

    # Remove the second last line
    del lines[-2]

    with open(file_path, 'w') as f:
        f.writelines(lines)


#this..
def deleteGraphFollowingJson(fname, tactic, vname):
  #fname is json name. vname is .v name
  fi = open(fname)
  data = json.load(fi)
  content = data[0]
  checkAndDelete = False
  fetchG = {}
  global proofGen
  #find first point where goal is not present. Keep deleting lines.
  for cc in reversed(content):

    if cc['_type'] == 'sentence' and 'Admitted' in cc['contents']:
      continue

    elif cc['_type'] == 'sentence' and checkAndDelete == False:
      #present goal that cannot be solved. Immediately above Admitted
      fetchG = cc['goals'][0]
      checkAndDelete = True
      #delete 2nd last from coq file
      #global proofGen
      proofGen = '\n'.join(proofGen.split('\n')[:-1])
      delete_second_last_line(vname)
      
    elif cc['_type'] == 'sentence' and len(cc['goals']) > 0: #potential parent tactic. Check the children
      checkPotentialMatch = False
      for gchild in cc['goals']:
        if gchild == fetchG: 
          #present. Keep moving up and deleting from proofGen
          proofGen = '\n'.join(proofGen.split('\n')[:-1]) 
          delete_second_last_line(vname)
          checkPotentialMatch = True
          break
      if checkPotentialMatch == False:
        #not present here. So, the goal point is already deleted.
        break #no need to delete anymore lines. Break out

  fi.close()

def exfalsoApplicationCheck(cg):
   #detects conclusion
  cgJson = json.loads(cg)
  listHypothesis = cgJson["hypotheses"]
  for hypoInd in listHypothesis:
    hypo = hypoInd["type"]
    hypoComp = " ".join(hypo.split())
    if "False <->" in hypoComp or "<-> False" in hypoComp or "-> False" in hypoComp:
      return True #exfalso can be applied
  return False

def checkBlowUp(cg, listGoals):
  #string version
  retGoal = ''
  conCg = countConclusion(cg)
  for child in listGoals:
    conChild = countConclusion(json.dumps(child))
    if conChild - conCg >= 300:
      retGoal = json.dumps(child)
      break
  return retGoal   

def checkWarningsOnly(msgGoal):
  if len(msgGoal) == 0:
    return True
  for gm in msgGoal:
    if "Warning:" not in gm["contents"]:
      return False #mesage present but not warning, so return false
  return True 

def pushUnsolvedInitial(content):
    proof_tree['start'] = []
    goal_errtac['start'] = []
    gen_tactics['start'] = ['-']

    #initial stack unsolved goals
    for hconc in content['goals']:
      goalOp = json.dumps(hconc)
      proof_tree['start'].append((goalOp,'-'))
      proof_tree[goalOp] = []
      goal_errtac[goalOp] = []
      gen_tactics[goalOp] = []
    #pdb.set_trace()
        
    
def pushGoal(cg,content,tac,fname,dt):
    
    listComp = dt[-5]['goals']
    listGoals = content['goals']
    tactic = tac[:-1]

    statusWarning = checkWarningsOnly(content["messages"])
    #len(content["messages"]) == 0 replaced by statusWarning == True
    #len(content["messages"]) > 0 replaced by statusWarning == False 
    if content["_type"] == "sentence" and statusWarning == True and len(content["goals"]) == 0:
      return ''

    elif tac == 'list_solve.' and content["messages"][-1]["contents"] == "nnnn":
      goalNotSolved = "Tactic list_solve could not solve the goal. \n"
      f.write("No Progress\n")
      f.write("Count: "+ str(count))
      f.write("\n----------------------------------------------------------\n")
      delete_second_last_line(fname)
      return goalNotSolved
    
    elif tac == 'list_solve.':
      #solved.
      return  ''
    
    #other than list_solve
    elif statusWarning == False and len(content["goals"]) > 0:
      goalNoProgress = "No progress made with tactic: "+ tac + "\n"
      f.write("No Progress\n")
      f.write("Count: "+ str(count))
      f.write("\n----------------------------------------------------------\n")
      delete_second_last_line(fname)
      return goalNoProgress
    
    elif statusWarning == False and len(content["goals"]) == 0: 
      goalError = "Tactic: "+ tactic + " application resulted in an error: "
      f.write("Error Tactic\n")
      f.write("Count: "+ str(count))
      f.write("\n----------------------------------------------------------\n")
      delete_second_last_line(fname)
      return goalError
    
    elif deepCompare(dt[-5], content):
      goalNoProgress = "No progress made with tactic: "+ tac + "\n"
      f.write("No Progress\n")
      f.write("Count: "+ str(count))
      f.write("\n----------------------------------------------------------\n")
      delete_second_last_line(fname)
      return goalNoProgress

    else:
      #makes progress, not error - push
      lenInsert = len(listGoals) - len(listComp) + 1
      if lenInsert <= 0:
        #print("solved.")
        return ''
      checkCycle = False
      retMsg = ''
      #lenInsert should be at least 1
      for index in range(0, lenInsert):
        lg = json.dumps(listGoals[index])
        if lg in proof_tree:
          checkCycle = True
          break
      if checkCycle == False:
        #no cycle. Insert children - checkBlowUp(cg,listGoals[:lenInsert])
        blowUpGoal =  checkBlowUp(cg,listGoals[:lenInsert])
        if len(blowUpGoal) > 0:
          #print("Oopps blowup")
          #goal_errtac[cg].append(tactic)
          #errSet = stringErrorRepOfTactics(cg)
          retMsg = 'Tactic: '+ tac + ' resulted in a more complex sub-goal: '+ blowUpGoal+'\n'
          f.write("Blowup Tactic\n")
          f.write("Count: "+ str(count))
          f.write("\n----------------------------------------------------------\n")
          delete_second_last_line(fname)
        else:
          #you can safely add. No blowup, no cycle
          for index in range(0, lenInsert):
            lg = json.dumps(listGoals[index])
            proof_tree[cg].append((lg, tactic))
            #new entry
            proof_tree[lg] = []
            goal_errtac[lg] = []
            gen_tactics[lg] = []
          for index in range(lenInsert, len(listGoals)):
            #insert further children, if applicable. Should not be the case
            lg = json.dumps(listGoals[index])
            if lg not in proof_tree:
              print("Should have been in proof tree.\n")
              pdb.set_trace()
              #proof_tree[cg].add((lg, tactic))
              #proof_tree[lg] = set()
              #goal_errtac[lg] = []
      else:
        #goal_errtac[cg].append(tactic)
        #errSet = stringErrorRepOfTactics(cg)
        retMsg = "Cyclic goal encountered with tactic: "+ tac + "\n"
        f.write("Cycle Tactic\n")
        f.write("Count: "+ str(count))
        f.write("\n----------------------------------------------------------\n")
        delete_second_last_line(fname)
      return retMsg

#main function   
if __name__ == '__main__':
  
  OPENAI_API_KEY = sys.argv[1]
  client = OpenAI(api_key=OPENAI_API_KEY)
  #models = OpenAI.Model.list()
  #pdb.set_trace()
  
  prompt = '''You are an expert in Coq, specifically in Separation Logic and the Verified Software Toolchain module. Please help me prove the correctness of Compcert C programs in VST (version 2.14) and Coq version 8.19.2, against the VST specification. 
It is recommended to use VST Floyd tactics like forward, forward_if, entailer!! etc. instead of using standard coq tactics to advance most of the proofs in this setting.  
Here are some additional definitions and axioms you may need to use that are not included in the VST codebase:
Fixpoint intersectTwo (l1 l2 : list Z) : list Z := 
  match l1 with 
  | nil => nil 
  | h :: l1' => if (existsb (fun y => h =? y) l2) then (h :: intersectTwo l1' l2) else  intersectTwo l1' l2
  end.

Fixpoint unionTwo (l1 l2 : list Z) : list Z := 
  match l1 with 
  | nil => l2
  | h :: l1' => if (existsb (fun y => h =? y) l2) then (unionTwo l1' l2) else (h :: unionTwo l1' l2)
  end.
 
Fixpoint setDiff (l1 l2 : list Z) : list Z := 
  match l1 with 
  | nil => nil
  | h :: l1' => if (existsb (fun y => h =? y) l2) then (setDiff l1' l2) else (h :: setDiff l1' l2)
  end.

Definition t_list := Tstruct _sll noattr.
Definition t_listc := Tstruct _sllc noattr.
Definition t_struct_tree := Tstruct _tree noattr.

Fixpoint listrep (sigma: list Z) (p: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, !! (Int.min_signed <= h <= Int.max_signed) && 
      data_at Tsh t_list (Vint (Int.repr h),y) p  *  listrep hs y
 | nil => 
    !! (p = nullval) && emp
 end.

Definition sllbox_rep (t: list Z) (b: val) :=
 EX p: val, data_at Tsh (tptr t_list) p b * listrep t p.

Fixpoint lseg (contents: list Z) (x z: val) : mpred :=
  match contents with
  | nil => !! (x = z) && emp
  | h::hs => EX y:val, !! (Int.min_signed <= h <= Int.max_signed) && 
             data_at Tsh t_list (Vint (Int.repr h), y) x * lseg hs y z
  end.

Definition key := Z.
Definition value := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> value -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : Z :=
  match t with
  | E => (-1)
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint lookupn (x: key) (t : tree) : bool :=
  match t with
  | E => false
  | T tl k v tr => if x <? k then lookupn x tl
                           else if k <? x then lookupn x tr
                           else true
  end.

Fixpoint isSkewed (t : tree) : Prop :=
  match t with
  | E => True
  | T tl k v tr => match (tl, tr) with 
                   | (E, _) => isSkewed tr 
                   | (_, E) => isSkewed tl 
                   | (_, _) => False 
                  end 
  end.

Fixpoint tree_rep (t: tree) (p: val) : mpred :=
  match t with
  | E => !!(p=nullval) && emp
  | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ Int.min_signed <= v <= Int.max_signed) &&
     EX pa:val, EX pb:val,
     data_at Tsh t_struct_tree (Vint (Int.repr x),(Vint (Int.repr v),(pa,pb))) p *
     tree_rep a pa * tree_rep b pb
  end.
 
Definition treebox_rep (t: tree) (b: val) :=
  EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.

Fixpoint insert (x: key) (v: Z) (s: tree) : tree :=
  match s with
  | E => T E x v E
  | T a y v' b => if  x <? y then T (insert x v a) y v' b
                         else if y <? x then T a y v' (insert x v b)
                         else T a x v b
  end.
 
Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
  match bc with
  | E => a
  | T b y vy c => T (pushdown_left a b) y vy c
  end.

Fixpoint inorderSuccessor (t: tree) : tree :=
  match t with
  | E => t
  | T lt k v rt => match lt with 
                   | E => t 
                   | _ => inorderSuccessor lt 
                   end
  end.

Fixpoint inorderSuccessorKey (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match lt with 
                    | E => k 
                    | _ => inorderSuccessorKey lt 
                    end
  end.

Fixpoint inorderMaxKey (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match rt with 
                   | E => k 
                   | _ => inorderMaxKey rt 
                   end
  end.

Fixpoint inorderSuccessorValue (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match lt with 
                   | E => v 
                   | _ => inorderSuccessorValue lt 
                   end
  end.

Fixpoint delete (x: key) (s: tree) : tree :=
  match s with
  | E => E
  | T a y v' b => if  x <? y then T (delete x a) y v' b
                         else if y <? x then T a y v' (delete x b)
                         else (match (a, b) with 
                              | (E, _) => b 
                              | (_, E) => a 
                              | (_, _) => let k' := inorderSuccessorKey b in 
                                         (let v'' := inorderSuccessorValue b in 
                                           T a k' v'' (delete k' b)
                                         )
                             end)
  end.

Fixpoint deleteWand (x: key) (s: tree) : tree :=
  match s with
  | E => E
  | T a y v' b => if  x <? y then T (deleteWand x a) y v' b
                         else if y <? x then T a y v' (deleteWand x b)
                         else (match (a, b) with 
                              | (E, _) => b 
                              | (_, E) => a 
                              | (_, _) => let xn := inorderSuccessor b in 
                                           match xn with 
                                           | E => b
                                           | T lt key v rt => T a key v (deleteWand key b)
                                           end  
                             end)
  end.

Fixpoint ForallS (t: tree) : Prop :=
  match t with
  | E => True
  | T l k v r => ((l = E) \/ (r = E)) /\ ForallS l /\ ForallS r
  end. 
  
Fixpoint ForallLookup (k' : key) (t: tree) : Prop :=
  match t with
  | E => False
  | T l k v r => (k = k') \/ ( k' < k /\ ForallLookup k' l) \/ (k' > k /\ ForallLookup k' r)
  end. 
  
Fixpoint ForallT (P: key -> Prop) (t: tree) : Prop :=
  match t with
  | E => True
  | T l k v r => P k /\ ForallT P l /\ ForallT P r
  end.

Inductive BST : tree -> Prop :=
  | BST_E : BST E
  | BST_T : forall l x v r,
      ForallT (fun y => y < x) l ->
      ForallT (fun y => y > x) r ->
      BST l ->
      BST r ->
      BST (T l x v r). 

Definition insListSpec (l : list Z) (t : tree) := fold_left (fun t k => insert k 0 t) l t.

Fixpoint insertarray (i : Z) (l : list Z) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insertarray i t
  end.

Fixpoint sortarr (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insertarray h (sortarr t)
  end.
  
Inductive sorted : list Z -> Prop :=
  | sorted_nil :
      sorted []
  | sorted_1 : forall x,
      sorted [x]
  | sorted_cons : forall x y l,
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Axiom existsbFalse: forall (A : Type) (f : A -> bool) (l : list A),
        ~(existsb f l = true) <-> ~(exists x : A, In x l /\ f x = true).

Axiom InNotIn: forall (l: list Z) (a1 a2: Z), In a1 l -> ~In a2 l -> a1 <> a2. 

Axiom intersectBothIn: forall (x: Z) (l1 l2: list Z), In x l1 -> In x l2 -> In x (intersectTwo l1 l2). 

Axiom intersectNotIn: forall (x: Z) (l1 l2: list Z), ~In x l1 \/ ~In x l2 -> ~In x (intersectTwo l1 l2). 

Axiom intersectProof: forall l1 l2, NoDup l1 -> NoDup l2 -> Forall (fun x => (In x (intersectTwo l1 l2)) <-> (Exists (fun y => x = y) l2)) l1. 

Axiom unionEitherIn: forall (l1 l2: list Z) (x : Z), In x l1 \/ In x l2 -> In x (unionTwo l1 l2). 

Axiom unionProof: forall l1 l2, NoDup l1 -> NoDup l2 -> Forall (fun x => In x (unionTwo l1 l2)) l1  /\ Forall (fun x => In x (unionTwo l1 l2)) l2.

Axiom setDiffProof: forall l1 l2, NoDup l1 -> NoDup l2 -> setDiff l1 l2 = filter (fun x => (negb (existsb (fun y => x =? y) l2))) l1.

Axiom exists_forall: forall h l, In h l <->  (existsb (fun y => h =? y) l = true).

Axiom notexists_forall: forall h l, ~In h l <->  (existsb (fun y => h =? y) l = false).

Axiom nullIsBST:  BST E.

Axiom leafIsBST: forall k v, BST (T E k v E).

Axiom lookupCorrectness: forall k t, BST t -> (lookupn k t = true <-> ForallLookup k t).

Axiom skewedCorrectness: forall t, (isSkewed t <-> ForallS t).

Axiom insertUBFacts: forall t x k v, 
ForallT (fun y => y < x) t -> k < x ->
ForallT (fun y => y < x) (insert k v t).

Axiom insertLBFacts: forall t x k v, 
ForallT (fun y => y > x) t -> k > x ->
ForallT (fun y => y > x) (insert k v t).

Axiom inorderSuccBaseCase: forall k v lr, inorderSuccessorKey (T E k v lr) = k.

Axiom inSuccLemma: forall k v lr lt' k' v' lr', inorderSuccessorKey (T (T lt' k' v' lr') k v lr) = inorderSuccessorKey (T lt' k' v' lr').

Axiom inMaxLemma: forall k v lt lt' k' v' lr', inorderMaxKey (T lt k v (T lt' k' v' lr')) = inorderMaxKey (T lt' k' v' lr').

Axiom inSuccNodeLemma: forall k v lr lt' k' v' lr', inorderSuccessor (T (T lt' k' v' lr') k v lr) = inorderSuccessor (T lt' k' v' lr').

Axiom forallLessThanProperty: forall t x, ForallT (fun y => y < x) t -> ForallT (fun y => y <= x) t.

Axiom forallGreaterThanProperty: forall t x, ForallT (fun y => y > x) t -> ForallT (fun y => y >= x) t.

Axiom succHelper: forall lt k v lr,  BST (T lt k v lr) -> (lt <> E) -> k > inorderSuccessorKey lt.

Axiom forallTProperty: forall t x k, x > k -> ForallT (fun y => y > x) t -> ForallT (fun y => y > k) t.

Axiom forallTLtProperty: forall t x k, x < k -> ForallT (fun y => y < x) t -> ForallT (fun y => y < k) t.

Axiom forallTGtNotProperty: forall t k, ForallT (fun y => y > k) t -> ForallT (fun y => y <> k) t.

Axiom forallTNotLtGtProperty: forall t k, ForallT (fun y => y <> k) t <-> ForallT (fun y => y < k \/ y > k) t. 

Axiom forallTLtNotProperty: forall t k, ForallT (fun y => y < k) t -> ForallT (fun y => y <> k) t.

Axiom inorderSuccRange: forall t lo hi, BST t -> t <> E -> ForallT (fun y => y > lo) t -> ForallT (fun y => y < hi) t -> 
lo < inorderSuccessorKey t < hi.

Axiom inorderSuccHi: forall t hi, BST t -> t <> E ->  ForallT (fun y => y < hi) t -> 
inorderSuccessorKey t < hi.

Axiom inorderSuccLo: forall t lo, BST t -> t <> E ->  ForallT (fun y => y > lo) t -> 
inorderSuccessorKey t > lo.

Axiom inorderMaxHi: forall t hi, BST t -> t <> E ->  ForallT (fun y => y < hi) t -> 
inorderMaxKey t < hi.

Axiom inorderMaxLo: forall t lo, BST t -> t <> E ->  ForallT (fun y => y > lo) t -> 
inorderMaxKey t > lo.

Axiom inorderSuccHelperRoot: forall lt k v lr,
BST (T lt k v lr) -> lt <> E -> inorderSuccessorKey (T lt k v lr) < k.

Axiom inorderSuccProperty: forall lr lt k v, BST (T lt k v lr) -> (lr <> E) ->
ForallT (fun y => y >= (inorderSuccessorKey lr)) lr /\ (k < (inorderSuccessorKey lr)).

Axiom minKeyProperty: forall t, BST t -> ForallT (fun y => y >= (inorderSuccessorKey t)) t.

Axiom maxKeyProperty: forall t, BST t -> ForallT (fun y => y <= (inorderMaxKey t)) t.

Axiom deleteUBFacts: forall t x k, 
BST t -> 
ForallT (fun y => y < x) t ->
ForallT (fun y => y < x) (delete k t).

Axiom deleteLBFacts: forall t x k, 
BST t -> 
ForallT (fun y => y > x) t ->
ForallT (fun y => y > x) (delete k t).

Axiom deleteNoDup: forall t k, BST t -> ForallT (fun y => y <> k) (delete k t).

Axiom insertPreservesBST: forall t k v, BST t -> BST (insert k v t).

Axiom forallTContradiction: forall t x, t <> E -> ForallT (fun y => y >= x) t -> ~ (ForallT (fun y => y < x) t). 

Axiom delKeyProperty: forall t k, BST t -> ForallT (fun y => y >= k) t -> ForallT (fun y => y > k) (delete k t).

Axiom deletePreservesBST: forall t k, BST t -> BST (delete k t).

Axiom insListDistribute : forall a l t, insListSpec (a :: l) t = insListSpec l (insert a 0 t).

Axiom insert_sorted: forall l a, sorted l -> sorted (insertarray a l).

Axiom sort_sorted: forall l, sorted (sortarr l).

Axiom sortedInSame: forall a l, In a (insertarray a l).

Axiom sortedInAdd: forall a x l, In a l -> In a (insertarray x l).

Axiom sortedInReverse: forall a x l, In a (insertarray x l) /\ (x <> a) -> In a l.

Axiom sortedMembership: forall x l, In x l <-> In x (sortarr l).

Axiom sortedNonMembership: forall x l, ~In x l <-> ~In x (sortarr l).

Axiom noDupInsertProof: forall a l, 
(~In a l /\ NoDup l) <-> NoDup (insertarray a l).

Axiom noDupSorted: forall l, NoDup l <-> NoDup (sortarr l).

Axiom lengthPlus1Insert: forall a l, Zlength (insertarray a l) = 1 + Zlength l. 

Axiom lengthPreservedSorted: forall l, Zlength (sortarr l) = Zlength l. 

Axiom sortedAll: forall l a, sorted(a :: l) <-> Forall (fun x => a <= x) l /\ sorted l. 

Axiom insertListSorted: forall l k v tl tr, Forall (fun x => k < x) l -> insListSpec l (T tl k v tr) = T tl k v (insListSpec l tr).

Axiom treeSkewed: forall l, NoDup l /\ sorted l -> isSkewed (insListSpec l E). 

Axiom relationPreservedSorted: forall l r, Forall r l <-> Forall r (sortarr l). 

Axiom nullContradiction: forall sh t v, data_at sh t v nullval = FF. 

Axiom listrep_local_facts:
 forall sigma p,
  listrep sigma p |--
  !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).

Axiom listrep_local_nonullfacts:
 forall sigma p,
  p <> nullval ->
  listrep sigma p |-- !! (sigma <> nil).

Axiom listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.

Axiom listrep_null: forall contents x,
  x = nullval ->
  listrep contents x = !! (contents=nil) && emp.

Axiom listrep_nonnull: forall contents x,
  x <> nullval ->
  listrep contents x =
    EX h: Z, EX hs: list Z, EX y:val,
      !! (contents = h :: hs) && !! (Int.min_signed <= h <= Int.max_signed) && 
      data_at Tsh t_list (Vint (Int.repr h), y) x * listrep hs y.

Axiom listrep_null_length: forall contents x,
  Zlength contents = 0 ->
  listrep contents x = !! (x = nullval) && !! (contents=nil) && emp.

Axiom listrep_nonnull_length: forall contents x,
  Zlength contents > 0 ->
  listrep contents x =
    EX h: Z, EX hs: list Z, EX y:val,
      !! (contents = h :: hs) && !! (Int.min_signed <= h <= Int.max_signed) && 
      data_at Tsh t_list (Vint (Int.repr h), y) x * listrep hs y.

Axiom singleton_lseg: forall (a: Z) (x y: val),
(Int.min_signed <= a <= Int.max_signed) -> 
lseg [a] x y = data_at Tsh t_list (Vint (Int.repr a), y) x.

Axiom lseg_app: forall (s1 : list Z) (b : Z) (x u: val),
(Int.min_signed <= b <= Int.max_signed) ->
lseg (s1 ++ [b]) x u = EX t: val, lseg s1 x t * data_at Tsh t_list (Vint (Int.repr b), u) t.

Axiom lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.

Axiom lseg_appgen: forall (s1 s2 : list Z) (x u: val),
lseg (s1 ++ s2) x u = EX t1: val, lseg s1 x t1 * lseg s2 t1 u.

Axiom lseg_listrep_equivalence: forall l p, 
lseg l p nullval = listrep l p.
   
Axiom tree_rep_saturate_local:
    forall t p, tree_rep t p |-- !! is_pointer_or_null p.

Axiom tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.

Axiom treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.

Axiom tree_contradict: forall k v t1 t2, 
!! (T t1 k v t2 = E) = FF.

Axiom tree_rep_null: forall t x,
  x = nullval -> 
  tree_rep t x = !! (t = E) && emp.

Axiom tree_rep_notnull: forall t x,
  x <> nullval ->
  tree_rep t x = EX k: Z, EX v: Z, EX a: tree, EX b: tree, EX pa:val, EX pb:val,
               !! (t = T a k v b) &&  !! (Int.min_signed <= k <= Int.max_signed /\ Int.min_signed <= v <= Int.max_signed) &&
    data_at Tsh t_struct_tree (Vint (Int.repr k),(Vint (Int.repr v),(pa,pb))) x *
    tree_rep a pa * tree_rep b pb.

Axiom treebox_rep_leaf: forall x p b v,
Int.min_signed <= v <= Int.max_signed ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (Vint (Int.repr v), (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.

Axiom typed_true_semcastCeq_eq:
  forall x y : val, typed_true tint 
  match sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y)) with 
  | Some v' => v'
  | None => Vundef
  end -> x = y.

Axiom typed_false_semcastCeq_eq:
  forall x y : val, typed_false tint 
  match sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y)) with 
  | Some v' => v'
  | None => Vundef
  end -> x <> y.

(*malloc and free are two functions available globally. The specifications are given below. These would help in calling the functions
and querying the appropriate lemmas*)  
Definition malloc_spec :=
  DECLARE _malloc
    WITH n: Z
    PRE [ tulong]
    PROP ()
    PARAMS (Vlong (Int64.repr n))
    SEP ()
    POST [ tptr tvoid ]
    EX v: val,
    PROP (malloc_compatible n v)
    RETURN (v)
    SEP (memory_block Tsh n v).

Definition free_spec :=
  DECLARE _free
  WITH p : val , n : Z
  PRE [ tptr tvoid]
  PROP() 
  PARAMS(p)
  SEP (memory_block Tsh n p)
  POST [ tvoid ]
  PROP () RETURN ( ) SEP ().

Given below are four examples of what the proof looks like, given the C program, respective Compcert AST and the specification written in VST. 
The proofs are annotated with comments (**) to help understand the thought process behind the tactics and/or lemmas used:
First example: 

C-code:
void swap(int *x, int *y) {
  int a = *x;
  int b = *y;
  *x = b;
  *y = a;
}

Compcert AST:
Definition f_swap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, tint) :: (_b, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _a (Ederef (Etempvar _x (tptr tint)) tint))
  (Ssequence
    (Sset _b (Ederef (Etempvar _y (tptr tint)) tint))
    (Ssequence
      (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b tint))
      (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a tint)))))
|}.

VST Specification: 
Definition swap_spec : ident * funspec :=
  DECLARE _swap
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr a)) y).


VST Proof:
Lemma swapSynth: semax_body Vprog Gprog f_swap swap_spec.
Proof.
  (*every proof in VST starts with the tactic start_function*)
  start_function.
  (*forward tactic tries to advance the proof in the forward direction *)
  forward. forward. forward. forward.
  (*conclusion of the goal has the shape _ |-- _ which represents an entailment. Here entailer! solves the goal and discharges the proof*)
  entailer!. 
Qed.

Second example:
void addAllElementsInRangeBy1(int a[], unsigned index, unsigned length) {
    if (index == length) {
        return;
    }
    a[index] = a[index] + 1;
    addAllElementsInRangeBy1(a, index + 1, length);
}

Compcert AST:
Definition f_addAllElementsInRangeBy1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_index, tuint) :: (_length, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _index tuint) (Etempvar _length tuint)
                 tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _index tuint)
            (tptr tint)) tint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _index tuint)
            (tptr tint)) tint)
        (Ebinop Oadd (Etempvar _t'1 tint) (Econst_int (Int.repr 1) tint)
          tint)))
    (Scall None
      (Evar _addAllElementsInRangeBy1 (Tfunction
                                        (Tcons (tptr tint)
                                          (Tcons tuint (Tcons tuint Tnil)))
                                        tvoid cc_default))
      ((Etempvar _a (tptr tint)) ::
       (Ebinop Oadd (Etempvar _index tuint) (Econst_int (Int.repr 1) tint)
         tuint) :: (Etempvar _length tuint) :: nil))))
|}.

VST Specification:
Definition addAllElementsInRangeBy1_spec : ident * funspec :=
  DECLARE _addAllElementsInRangeBy1
    WITH a: val, sh : share, contents : list Z, ind : Z, length : Z
     PRE [ tptr tint, tuint, tuint ]
     PROP  (writable_share sh; Zlength contents = length;
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
        Forall (fun x => Int.min_signed <= x + 1 <= Int.max_signed) (sublist ind length contents))
     PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
     SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
     POST [ tvoid ]
     PROP ()
     RETURN ()
     SEP (data_at sh (tarray tint length) (map Vint (map Int.repr ((sublist 0 ind contents) ++ map (fun x => x + 1) (sublist ind length contents)))) a).

VST Proof:
Lemma addAllElementsInRangeBy1Synth: semax_body Vprog Gprog f_addAllElementsInRangeBy1 addAllElementsInRangeBy1_spec.
Proof.
  start_function.
  forward_if.
  + forward.
  (*Here the goal is of the shape of entailment, but entailer! or entailer!! doesn't solve the goal. list_solve however solves it, as it involves lists*)
  list_solve.
  + forward. forward.
    - entailer!!. 
  (*The conclusion of the goal is: Int.min_signed <= Int.signed (Int.repr (Znth ind contents)) + Int.signed (Int.repr 1) <= Int.max_signed. We rewrite with Int.signed_repr. This rewrite gets rid of the wrapper Int.signed (Int.repr _) and produces a side condition on an element of the list contents (Znth ind contents) that can be discharged with list_solve*)
  rewrite Int.signed_repr by list_solve.
  (*After the previous rewrite, the conclusion of the goal is: Int.min_signed <= Znth ind contents + Int.signed (Int.repr 1) <= Int.max_signed. This rewrite is on the constant 1, the side condition of which can be discharged with rep_lia*)
  rewrite Int.signed_repr by rep_lia.
  (*Now that the goal is free of wrappers, it can be discharged withlist_solve*)
  list_solve.
  (*The conclusion is a function call. The contents of the list is ( upd_Znth ind contents (Znth ind contents + 1)). However, the the data_at clause has the form: (upd_Znth ind (map Vint (map Int.repr contents))(Vint (Int.add (Int.repr (Znth ind contents)) (Int.repr 1)))), which doesn't have exactly this shape. We transform the data_at list by removing the wrappers with some rewrites to bring it to the exact shape before passing it to function call *)
 (*This rewrite removes Int.add (Int.repr _) wrapper*)
  - rewrite !add_repr.
  (*puts the map outside of upd_Znth. After this, we get it in the exact shape, by removing the reprs and map*)
  rewrite !upd_Znth_map.
  forward_call(a, sh, upd_Znth ind contents (Znth ind contents + 1), ind + 1, length).
    * split.
      ** list_solve.
      ** split.
         *** list_solve.
         *** list_solve.
   * entailer!!. list_solve.
Qed.


Third example:

C code: 
bool allNumsSame(int a[], unsigned ind, unsigned length) {
    if (ind >= length - 1) {
        return true;
    }
    else if (a[ind] != a[ind + 1]) {
        return false;
    }
    else {
         return allNumsSame(a, ind + 1, length);
    }
}

Compcert AST:
Definition f_allNumsSame := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_ind, tuint) :: (_length, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: (_t'3, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oge (Etempvar _ind tuint)
               (Ebinop Osub (Etempvar _length tuint)
                 (Econst_int (Int.repr 1) tint) tuint) tint)
  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _ind tuint)
          (tptr tint)) tint))
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Etempvar _a (tptr tint))
            (Ebinop Oadd (Etempvar _ind tuint) (Econst_int (Int.repr 1) tint)
              tuint) (tptr tint)) tint))
      (Sifthenelse (Ebinop One (Etempvar _t'2 tint) (Etempvar _t'3 tint)
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        (Ssequence
          (Scall (Some _t'1)
            (Evar _allNumsSame (Tfunction
                                 (Tcons (tptr tint)
                                   (Tcons tuint (Tcons tuint Tnil))) tbool
                                 cc_default))
            ((Etempvar _a (tptr tint)) ::
             (Ebinop Oadd (Etempvar _ind tuint)
               (Econst_int (Int.repr 1) tint) tuint) ::
             (Etempvar _length tuint) :: nil))
          (Sreturn (Some (Etempvar _t'1 tbool))))))))
|}.

VST Specification:
Definition allNumsSame_spec : ident * funspec :=
  DECLARE _allNumsSame
  WITH a : val, sh : share, contents : list Z, ind : Z, length : Z
  PRE [ tptr tint, tuint, tuint ]
  PROP  (readable_share sh; Zlength contents = length;
	0 <= length <= Int.max_unsigned; 0 <= ind < length;
	Forall (fun x =>  Int.min_signed <= x <= Int.max_signed) contents)
  PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
  SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
  POST [ tbool ]
  EX bv: bool,
    PROP ((Forall (fun x => x = Znth ind contents) (sublist ind length contents)) <-> (bv = true))
    RETURN (bool2val bv)
    SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).


VST Proof:
Lemma allNumsSameSynth: semax_body Vprog Gprog f_allNumsSame allNumsSame_spec.
Proof.
  start_function.
  (*The conclusion of the goal is in the shape of if then else, which is also the last command of the program, i..e, no additional commands follow if-then-else, so the forward-if tactic works here. However, if there is a  statement folliwng if-then-else, then it is recommended to apply the theorem semax_if_seq followed by forward_if. Do not infer the joint postcondition of if-then-else*)
  forward_if.
  + forward.
  (*The conclusion is the form of an entailment but also requires instantiation of an existential variable. In this case, a0 is true. We can infer it from a0 = true in right side of the entailment, and instantiate with that*)
  Exists true.
  entailer!!.
  (*The conclusion is of the form _ <-> _, so we do split and intros*)
  split.
   - intros.
  (*the left and right side of the goal are equal, so reflexivity discharges it*)
  reflexivity.
  (*list_solve can be used to completely solve goals that involve quantifiers and lists. Here it discharges the entire goal after intros. Only use list_solve if it discharges the entire goal*)
  - intros. list_solve.
    + forward. forward. forward_if.
  - forward. Exists false. entailer!!.
    (*The conclusion of the goal has the form _ <-> _. Hence, we split*)
    split.
         * (*The conclusion of the goal has the form _ -> _, hence we intros to shift the left part of the implication to the hypothesis*) intros. list_solve.
         * intros. list_solve.
  (*The conclusion is of the shape of a function call: _t'1 = _allNumsSame([(_a)%expr; (_ind + (1))%expr; (_length)%expr]). Here, we specify the parameters in the order of the specification, which is: val, share, list Z, Z, Z*)
  - forward_call(a, sh, contents, ind + 1, length).
    Intros vret. forward.
    Exists vret. entailer!!. split. 
    * split.
      *** intros. 
  (*Part of the goal looks like: [H5: Forall (fun x : Z => x = Znth (ind + 1) contents) sublist (ind + 1) (Zlength contents) contents) <-> vret = true; H9: Forall (fun x : Z => x = Znth ind contents)(sublist ind (Zlength contents) contents) |- vret = true]. H5 matches with the conclusion and can be applied. We choose this as the premise of H5 has the shape that matches with H9, which will help discharge this goal*)
     apply H5.
  (*The conclusion now: Forall (fun x : Z => x = Znth (ind + 1) contents)(sublist (ind + 1) (Zlength contents) contents) and H9 have the same shape except the goal starts at index (ind + 1) and H9 starts from ind. So, we rewrite using sublist_split in H9, that splits into a singleton list and the rest starting from (ind + 1). We rewrite it using list_solve that helps discharge side conditions of the rewrite*)
  rewrite sublist_split with ind (ind + 1) (Zlength contents) contents in H9 by list_solve.
  (*Forall_app would split the ++ into two lists inside the Forall quantifier. This helps us getting the hypothesis that matches the conclusion, and can be discharged using destruct and assumption, or list_solve*)
  apply Forall_app in H9. destruct H9 as [? ?]. list_solve.
  (*applying H5 in H9 helps get the premise similar in shape, differing in indices with the present goal*)
  *** intros. apply H5 in H9.
  (*we split at the conclusion as the conclusion starts at ind and H9 starts at (ind + 1)*)
  rewrite sublist_split with ind (ind + 1) (Zlength contents) contents by list_solve.
  apply Forall_app. split.
  (*list_solve fully solves this goal*)
  **** list_solve.
  (*Part of the goal looks like this: [H4 : Int.repr (Znth ind contents) = Int.repr (Znth (ind + 1) contents); H9: Forall (fun x : Z => x = Znth (ind + 1) contents)(sublist (ind + 1) (Zlength contents) contents) |- Forall (fun x : Z => x = Znth ind contents)(sublist (ind + 1) (Zlength contents) contents)] The conclusion now differs from H9 with respect to x = Znth (ind + 1) contents in H9, and  x = Znth ind contents in the goal. From H4, we know that the two are equal, but cannot directly rewrite as they are wrapped inside Int.repr. Hence apply the lemma repr_inj_signed to obtain the equality. It produces sub conditions that can be discharged by list_solve*)
  **** apply repr_inj_signed in H4.
       ***** list_solve.
       ***** list_solve.
       ***** list_solve.
  (*vret is a boolean, so destructing and simplifying it will discharge the goal for the two cases*)
    * destruct vret.
      ** simpl.  reflexivity.
      ** simpl. reflexivity.
Qed.

Fourth example:

C code: 
struct sll* addLast(struct sll* h, int value) {
    if (h == NULL) {
        struct sll* new_node = (struct sll*) malloc(sizeof(struct sll));
        new_node->key = value;
        new_node->next = NULL;
        return new_node;
    } else {
        h->next = addLast(h->next, value);
        return h;
    }
}

Compcert AST:
Definition f_addLast := {|
  fn_return := (tptr (Tstruct _sll noattr));
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _sll noattr))) :: (_value, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_node, (tptr (Tstruct _sll noattr))) ::
               (_t'2, (tptr (Tstruct _sll noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _sll noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _sll noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _sll noattr) tulong) :: nil))
      (Sset _new_node
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _sll noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _new_node (tptr (Tstruct _sll noattr)))
            (Tstruct _sll noattr)) _key tint) (Etempvar _value tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _new_node (tptr (Tstruct _sll noattr)))
              (Tstruct _sll noattr)) _next (tptr (Tstruct _sll noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Sreturn (Some (Etempvar _new_node (tptr (Tstruct _sll noattr))))))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _h (tptr (Tstruct _sll noattr)))
              (Tstruct _sll noattr)) _next (tptr (Tstruct _sll noattr))))
        (Scall (Some _t'2)
          (Evar _addLast (Tfunction
                           (Tcons (tptr (Tstruct _sll noattr))
                             (Tcons tint Tnil)) (tptr (Tstruct _sll noattr))
                           cc_default))
          ((Etempvar _t'3 (tptr (Tstruct _sll noattr))) ::
           (Etempvar _value tint) :: nil)))
      (Sassign
        (Efield
          (Ederef (Etempvar _h (tptr (Tstruct _sll noattr)))
            (Tstruct _sll noattr)) _next (tptr (Tstruct _sll noattr)))
        (Etempvar _t'2 (tptr (Tstruct _sll noattr)))))
    (Sreturn (Some (Etempvar _h (tptr (Tstruct _sll noattr)))))))
|}.

VST Specification:
Definition addLast_spec :=
  DECLARE _addLast
    WITH p: val, l: list Z, v: Z
    PRE  [ tptr t_list, tint ]
    PROP(Forall (fun x => Int.min_signed <= x <= Int.max_signed) l;
         Int.min_signed <= v <= Int.max_signed)
    PARAMS (p; Vint (Int.repr v))
    SEP (listrep l p)
    POST [ tptr t_list ]
    EX c:val,
    PROP()
    RETURN(c)
    SEP (listrep (l ++ [v]) c).

VST Proof:
Lemma addLastSynth: semax_body Vprog Gprog f_addLast addLast_spec.
Proof.
  start_function. forward_if.
  + forward_call(sizeof(Tstruct _sll noattr)). Intros vret.
  (*One of the SEP predicates of the conclusion is: memory_block Tsh (sizeof (Tstruct _sll noattr)) vret. This is memory_block instead of data_at, so we perform rewrite with the lemma memory_block_data_at_ to change the format to data_at. The sidecondition produced is resolved by auto*)
  rewrite memory_block_data_at_ by auto. forward. forward. forward.
  (*Existential variable a here needs to be instantiated. Here we instantiate with vret, from the relation (vret = a) from the right side of the entailment*)
  Exists vret. entailer!!. 
  (*Part of the goal looks like: [H5 : nullval = nullval <-> l = [] |- data_at Tsh (Tstruct _sll noattr) (Vint (Int.repr v), Vlong (Int64.repr 0)) vret * listrep l nullval |-- listrep (l ++ [v]) vret]. entailer!! or list_solve does not discharge the goal. There is heaplet stating listrep l nullval. The address nullval indicates l must be an empty list, therefore we rewrite with the axiom listrep_null with nullval as the address.*)
  rewrite (listrep_null _ nullval) by auto. entailer!!.
  (*The conclusion of the goal contains listrep ([] ++ [v]) vret, which can be simplified to remove the [] list by simpl*)
  simpl. 
  (*y is an existential of type val, which should be nullval, following from !! (y = nullval) occuring in the right hand side of the entailment*)
  Exists nullval. entailer!!.
  (*The forward tactic here fails to make progress as it does not know whether p (pointed by h) is a valid address. From H1, we know that p <> nullval, and we have the axiom listrep_nonnull that proves its validity. Hence, we rewrite with the axiom with p. The side conditions are proven by auto*)
  + rewrite (listrep_nonnull _ p) by auto.
  Intros h hs y.
  (*After the rewrite and intros of variables, forward can make progress*)
  forward. forward_call(y, hs, v).
  (*Part of the goal looks like: [H : Forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) l; H2 : l = h :: hs |- Forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) hs]. list_solve directly does not solve the goal. However, H has a similar shape, and We rewrite H2 to H, to reflect l has a cons structure with hs being the list. list_solve then discharges the goal completely*)
  - rewrite H2 in H. list_solve.
  - Intros vret. forward. forward. Exists p. entailer!!. (*The conclusion of the goal is: listrep (hs ++ [v]) vret * data_at Tsh t_list (Vint (Int.repr h), vret) p |-- listrep ((h :: hs) ++ [v]) p. The rhs of the entailment has a cons structure, which needs to be unfolded and the existential from the unfolding needs to be instantiated. simpl does the unfolding of cons and introduces the appropriate existentials to instantiate, for the proof to go through*) simpl.
 (*The rhs of the entailment is: EX y0 : val, !! (Int.min_signed <= h <= Int.max_signed) && data_at Tsh t_list (Vint (Int.repr h), y0) p * listrep (hs ++ [v]) y0. y0 is instantiated to vret by looking at the heaplet data_at Tsh t_list (Vint (Int.repr h), vret) p on the left and data_at Tsh t_list (Vint (Int.repr h), y0) p on the right. Here, p is the address representing the node, on both sides, so the node contents must be the same. *)
  Exists vret. entailer!!.
Qed.
'''
  
  files = [sys.argv[2]]

  #files = ['countOccurence.v']
  countFiles = 0
  for fn in files:
    errTactics = []
    proof_tree = {} #parent goal to children goals
    goal_errtac = {} #tried tactics that resulted in a failed goal
    gen_tactics = {} #list of tactics generated for each goal.
    #for every file, assign proofGen and llmProofGen to empty strings.
    proofGen = ''
    llmProofGen = ''
    countFiles += 1
    print("File: ",fn, "Number: ", countFiles)
    #initial run
    fl_vname = fn
    fl_jname = fl_vname[:-1]+"json"
    fl_tname = fl_vname[:-1]+"txt"
    start_time = time.perf_counter()
    insert_before_last_line("proofs/"+fl_vname,'start_function. progltac false false _free 0.')
    #run alectryon initially, with startfunction and sepauto_simpl
    subprocess.run(["alectryon", "--frontend", "coq", "--backend", "json", "-Q", ".", "GenProof", "proofs/"+fl_vname, "-o", "proofs/"+fl_jname])
    #exit()
    #fo is reading of json, f is the log file
    fo = open("proofs/"+fl_jname)
    f = open("prooflogs/"+fl_tname,"w")
    data = json.load(fo)
    content = data[0][-3] #proof tactic before before admitted.
    if len(content["goals"]) == 0:
       #print("Completely solved by sepauto")
       f.write("Solved fully by sepauto\n")
       end_time = time.perf_counter()
       #calculate the time difference - wall clock time
       time_diff = end_time - start_time
       f.write("Wall clock time elapsed: "+str(time_diff)+" seconds\n")
       f.close()
       fo.close()
       continue
    #pushes all the unsolved goals. Populates proof_tree
    pushUnsolvedInitial(content)
    #pdb.set_trace()
    #proofGen = ''
    fo.close()
    #travstack is initialized to start
    travstack = ['start']

    #read benchmark instruction. This also contains the CompCert AST and VST spec - proofGenPrompt.
    with open("proverLLMSpec/"+fl_tname, 'r', encoding='utf-8') as file:
      userinst = file.read()
    messages=[
      {"role": "developer", "content": prompt},
      {"role": "user", "content": userinst},
    ]
    count = 0
    #synerr = 0
    prevtactic = ''
    ctactic = ''
    while len(travstack) > 0 and count < 50: 
      currP = '''Given the goal below, predict the next set of tactics to advance the goal. 
      You must predict at most five tactics, all of whom only advance this goal by one step (i.e., all the tactics should independently advance the goal by one step. 
      They won't be applied in sequence), in order of highest probability of success - i.e., if you predict three tactics: a.,b., and c. then tactic a has the highest chance of success, 
      and c, the lowest. Again, the tactics are applied independently, i.e., either a, or b, or c, not in sequence like: a;b;c. Hence, predict tactics that can advance the goal independently and not in sequence.   
      Every tactic must end with the delimiter '.', and the tactics must be separated by the delimeter ';'. For the example above, the response should look like: a.;b.;c.
      Please do not use a set of tactics grouped by semicolons as one tactic - i.e., split; intros. is not allowed. split. or, intros. is allowed.
      The destruct tactic must always be accompanied by an eqn:. You should instantiate an existential with the appropriate value, and 
      not predict eexists. You should also not predict the simple_if_tac tactic, 
      or any tactic that loses information. The tactics should not be surrounded by quotation, or any other unnecessary command that'd trigger a syntax error. 
      If the goal cannot be solved, please respond with 'Unsolvable.'.
      No other information is needed.  \n\n'''
      #pek the stack - first element. Go through the children
      parGoal = travstack[-1]
      checkUnsolvable = False #gpt gives up - predicts unsolvable goal.
      #generate it regardless
      #children = proof_tree[parGoal]
      print("File: ",fn, "Number: ", countFiles, "Count: ", count)
      while len(proof_tree[parGoal]) > 0:
        if count >= 50:
           break
        #print("Starting fresh child.")
        #goal under investigation. For which tactics will be generated - keep taking the first goal, as they will be deleted,
        cg, tacPar = proof_tree[parGoal][0]
        errSet = stringErrorRepOfTactics(cg)
        errMsg = ''
        if len(errSet) > 0:
          errMsg = 'The list of known, erroneous tactics generated for this goal is: '+errSet+'. The tactics predicted by you should not be part of this list.'
        if travstack[-1] != cg:
          travstack.append(cg)
        ctactic = ''
        #initialize erros to nill
        goal_errtac[cg] = []
        f.write(cg)
        f.write("\n")
        extraMsg = ''
        #while (count < 100): 
        #subprocess.run(["alectryon", "--frontend", "coq", "--backend", "json", "-Q", ".", "LLMSynth", "proofs/"+fl_vname, "-o", "proofs/"+fl_jname])
        fullAndCorrectProof = 'The full proof generated by you so far is: \n'+llmProofGen+' The correct proof generated by you so far is: \n'+proofGen
        LLMPrompt = currP + extraMsg + cg + errMsg + '\n Report Unsolvable if the goal cannot be solved' + fullAndCorrectProof
        messages.append({"role":"user","content":LLMPrompt})
        ctacticList = []
        #while count < 50:
          #subprocess.run(["alectryon", "--frontend", "coq", "--backend", "json", "-Q", ".", "LLMSynth", "proofs/"+fl_vname, "-o", "proofs/"+fl_jname])
        completion = client.chat.completions.create(
            model="gpt-5-mini-2025-08-07", 
            seed=84328890114,
            #temperature=0.3,
            messages=messages
        )
        ct = completion.choices[0].message.content
        cp2 = ct.replace('\n','')
        cp1 = cp2.replace('```coq','')
        ctac = cp1.replace('```','')
        tmp1 = ctac.split(".")
        ctacticList = ctac.split(";")
        
        gen_tactics[cg] = ctacticList
        #print("tactics generated: ",ctacticList)
        count += 1
        while len(gen_tactics[cg]) > 0 and count < 50: 
          #removes the tactic at the beginning - going by probability
          ctac1 = gen_tactics[cg].pop(0)
          ctac = " ".join(ctac1.split()) #
          prevtactic = ctactic 
          ctactic = ctac[:-1]
          #print("Tactic: ",ctac)
          #ctactic = ctac[:-1]
          llmProofGen = llmProofGen + ctac + '\n'
          #tactic that can make potential progress 
          tacProgress = ''
          checkAcceptable = True #no real progress.
          checkUnsolvable = False
          #genTacs = stringErrorRepOfTactics(cg)
          if ctactic in goal_errtac[cg]:
            #generates previously rejected error, or no progress tactics in cg
            checkAcceptable = False
            extraMsg = 'Tactic: '+ ctactic + ' has been previously generated for this goal, and was not successful.\n'
            f.write("Repeated Error Tactic: "+ ctactic + "\n")
            f.write("Count: "+ str(count))
            f.write("\n----------------------------------------------------------\n")

          if 'symmetry' in prevtactic and 'symmetry' in ctactic:
            #two consecutive symmetries don't do anything
            checkAcceptable = False
            goal_errtac[cg].append(ctactic)
            extraMsg = 'Tactic: '+ ctactic + ' was immediately tried before, which creates a cycle.\n'
            f.write("Cycle Tactic: "+ ctactic + "\n")
            f.write("Count: "+ str(count))
            f.write("\n----------------------------------------------------------\n")

          elif 'Unsolvable' in ctactic and tacPar != '-': 
            #predicts Unsolvable. Need to delete - not a result of -, Par tctic
            #print("Unsolvable detected.")
            checkUnsolvable = True
            #save the set of error tactics
            listOfErrorTacs = goal_errtac[parGoal]
            #append tacPar as it generates unsolvable goal - check here.
            listOfErrorTacs.append(tacPar)
            #delete all children of tacPar from the proofTree from cg. Successful children of cg have already been deleted
            for gDelete in proof_tree[parGoal]:
              #delete from parGoal's children
              goalToDel, goalToDelTac = gDelete
              #delete from proof_tree and goal_errtac - these will not have children as these are recently added.
              del proof_tree[goalToDel]
              del goal_errtac[goalToDel]
              if goalToDel in gen_tactics:
                del gen_tactics[goalToDel]

            deleteGraphFollowingJson("proofs/"+fl_jname,tacPar,"proofs/"+fl_vname)
            proof_tree[parGoal] = []
            goal_errtac[parGoal] = listOfErrorTacs
            #pop cg off the stack.
            popcg = travstack.pop()
            if popcg != cg:
              pdb.set_trace()
            #get the list
            #genTacs = stringErrorRepOfTactics(parGoal)
            extraMsg = 'Tactic: '+ tacPar + ' resulted in the sub-goal: '+cg + '\nbeing unsolvable.\n'
            cg = parGoal
            #grandma
            parGoal = travstack[-2]
          elif 'simple_if_tac' in ctactic:
            #destruct without equation.
            checkAcceptable = False
            goal_errtac[cg].append(ctactic)
            extraMsg = 'simple_if_tac cannot be applied, as it would lose information. \n'
            f.write("Information Loss Tactic: "+ ctactic + "\n")
            f.write("Count: "+ str(count))
            f.write("\n----------------------------------------------------------\n")

          elif 'destruct' in ctactic and ('eqn' not in ctactic):
            checkAcceptable = False
            goal_errtac[cg].append(ctactic)
            extraMsg = 'Tactic destruct needs to be supported with an equation. \n'
            f.write("Information Loss Tactic: "+ ctactic + "\n")
            f.write("Count: "+ str(count))
            f.write("\n----------------------------------------------------------\n")

          elif 'exfalso' in ctactic and (not exfalsoApplicationCheck(cg)):
            #exfalso cannot be applied
            checkAcceptable = False
            goal_errtac[cg].append(ctactic)
            extraMsg = 'exfalso cannot be applied for this goal, as it would lose information. \n'
            f.write("Information Loss Tactic: "+ ctactic + "\n")
            f.write("Count: "+ str(count))
            f.write("\n----------------------------------------------------------\n")


          elif ctactic == "list_solve":
            tacProgress = 'tryif solve[list_solve] then idtac "yyyy" else idtac "nnnn".'
          else:
            tacProgress = 'tryif (progress timeout 30 ('+ ctactic + '; progltac false false _free 0)) then idtac else (idtac "aaaa";timeout 30 '+ctactic+').'
          #unacceptable: try again: 
          if checkAcceptable == False:
             #messages.pop()
             continue
          elif checkUnsolvable == True:
             #print("Unsolvable predicted.\n")
             f.write("Backtrack: "+ ctactic + "\n")
             f.write("Count: "+ str(count))
             f.write("\n----------------------------------------------------------\n")
             #changed json here
             subprocess.run(["alectryon", "--frontend", "coq", "--backend", "json", "-Q", ".", "GenProof", "proofs/"+fl_vname, "-o", "proofs/"+fl_jname], check=True, capture_output=True, text=True)
             continue
          elif checkUnsolvable == False and 'Unsolvable' in ctactic:
            extraMsg = 'You predicted unsolvable. However, this goal is definitely solvable \n.'
            goal_errtac[cg].append(ctactic)
            f.write("Wrong Backtrack: "+ ctactic + "\n")
            f.write("Count: "+ str(count))
            f.write("\n----------------------------------------------------------\n")
            #messages.pop()
            #exit()
            continue
          else:
          
            insert_before_last_line("proofs/"+fl_vname,tacProgress)
            try:
              subprocess.run(["alectryon", "--frontend", "coq", "--backend", "json", "-Q", ".", "GenProof", "proofs/"+fl_vname, "-o", "proofs/"+fl_jname], check=True, capture_output=True, text=True)
              #non errnoneous tactic application
              fo = open("proofs/"+fl_jname)
              data = json.load(fo)
              content = data[0][-3] #proof tactic before before admitted.
              #if len(content['goals']) == 0:
                #break
              extraMsg = pushGoal(cg,content,ctac,"proofs/"+fl_vname,data[0])
              #delete cg's children...
              cgChildren = proof_tree[cg]
              checkProgress = True

              if len(extraMsg) > 0: #no progress - syntactic, semantic, cycle, blowup, all
                #print("No progress. Trying again.\n")
                checkProgress = False #try again
                
              #cg is solved
              elif len(cgChildren) == 0 and len(extraMsg) == 0:
                #pop cg from the stack
                #proofGen = proofGen + ctac + '\n'
                popcg = travstack.pop()
                if popcg != cg:
                  pdb.set_trace()
                #delete cg from the tree
                del proof_tree[cg]
                #no need to keep errtac as well
                del goal_errtac[cg]
                #delete all generated, and or proposed tactics 
                del gen_tactics[cg]
                #delete cg's entry from its parent => cg will be the first index. You proceed left to right 
                proof_tree[parGoal].pop(0)
              

              fo.close()
              if checkProgress == True:
                #write write
                f.write("Progress Tactic: "+ ctactic)
                f.write("\n")
                f.write("Count: "+ str(count))
                f.write("\n----------------------------------------------------------\n")
                
                if proofGen != '':
                  proofGen = proofGen + '\n' + ctac
                else:
                  proofGen = ctac
                break
              else:
                #print("Try again..") 
                goal_errtac[cg].append(ctactic)

            except Exception as e:
              #exception caught
              #print("Error is here. Need to try again\n")
              fo = open("proofs/"+fl_jname)
              data = json.load(fo)
              contentLast = data[0][-1]
              goal_errtac[cg].append(ctactic)
              if contentLast["contents"] != "Admitted.":
                #print("Insufficient arguments")
                extraMsg = "Tactic: "+ ctac + " application resulted in an error. It needs more arguments. \n"
                #stack.append(goalError)
                f.write("Error Tactic: "+ ctactic + "\n")
                f.write("Count: "+ str(count))
                f.write("\n----------------------------------------------------------\n")
                delete_second_last_line("proofs/"+fl_vname)
              else:
                content = data[0][-3]
                extraMsg = pushGoal(cg,content,ctac,"proofs/"+fl_vname,data[0])
              #run before moving on to the next tactic. So that the json is updated with the correct file
              subprocess.run(["alectryon", "--frontend", "coq", "--backend", "json", "-Q", ".", "GenProof", "proofs/"+fl_vname, "-o", "proofs/"+fl_jname], check=True, capture_output=True, text=True)
              fo.close()

        #if checkUnsolvable == True:
          #break
        messages.pop()
        #done with cg - forever (popped out), or for now. 
        #Check the top of the stack - if it does not have any children, then delete it
        #for loop iteration next
        if travstack[-1] == parGoal and len(proof_tree[parGoal]) == 0:
          #print("All children explored.")
          break #all children of parGoal are done. Break. Go to parGoal's parent.
        elif travstack[-1] != parGoal and len(proof_tree[travstack[-1]]) > 0: #a child of parGoal got pushed - cg, which has cildren. So, you break and recurse from the child 
          #print("New child inserted due to progress.")
          break
        elif travstack[-1] != parGoal:
          #no children generated - but still in stack. This means we need to try again
          #print("Need to try again")
          popcg = travstack.pop() #pop cg. We do not delete it from parGoal.
          break
        #else: #parGoal still has unexplored children.
          #print("Going to the next child.")
          #children = proof_tree[parGoal]

      #parGoal is done - all its children are also gone. Nothing is pushed. Otherwise start from the child goal cg. While loop next
      if travstack[-1] == parGoal and len(proof_tree[parGoal]) == 0:
        #print("Popping parent.\n")
        del proof_tree[parGoal]
        del goal_errtac[parGoal]
        del gen_tactics[parGoal]
        #pop parent goal coz it is on top of the stack
        popPar = travstack.pop()
        if len(travstack) > 0:
          #parent of parGoal
          gPar =  travstack[-1]
          #delete parGoal from gPar
          tacDel = ''
          pG, td = proof_tree[gPar][0]
          if pG != parGoal:
            pdb.set_trace()
          proof_tree[gPar].pop(0)
          #for tacDelete in list(proof_tree[gPar]):
            #pg, tacDel = tacDelete
            #break
          #delete parGoal and tacDel
          #proof_tree[gPar].pop(0)
          #proof_tree[gPar].remove((parGoal,tacDel))

    end_time = time.perf_counter()
    time_diff = end_time - start_time
    f.write("Wall clock time elapsed: "+str(time_diff)+" seconds\n")    
    f.close()  
    print(count)



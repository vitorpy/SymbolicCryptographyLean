import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card


import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Core.Fixpoints

-- The definition of symbolic indistinguishability consists of 3 parts
-- (i) Normalization, i.e. performing simple computations on the expressions
-- (ii) Variable renaming -- both key and bit variables.
-- (iii) Adversary view, i.e. hiding the parts of the expression that are not accessible to the adversary.

-- First, we define all those three parts, and then we combine them into the definition of symbolic indistinguishability.

-- Part i.  Normalization

def normalizeB (p : BitExpr) : BitExpr :=
  match p with
  | BitExpr.Not (BitExpr.Not e) => normalizeB e
  | BitExpr.Not (BitExpr.Bit b) => BitExpr.Bit (not b)
  | e => e

def normalizeExpr {s : Shape} (p : Expression s) : Expression s :=
  match p with
  | Expression.BitE p => Expression.BitE (normalizeB p)
  | Expression.Perm (Expression.BitE b) p1 p2 =>
    let b' :=  normalizeB b
    let p1' := normalizeExpr p1
    let p2' := normalizeExpr p2
    match b' with
    | BitExpr.Bit b'' =>
      if b''
      then Expression.Pair p2' p1'
      else Expression.Pair p1' p2'
    | BitExpr.Not b'' =>
      Expression.Perm (Expression.BitE b'') p2' p1'
    | BitExpr.VarB k => Expression.Perm (Expression.BitE (BitExpr.VarB k)) p1' p2'
  | Expression.Pair p1 p2 => Expression.Pair  (normalizeExpr p1) (normalizeExpr p2)
  | Expression.Enc k e => Expression.Enc k (normalizeExpr e)
  | p => p

-- Part ii. Variable renaming

-- We start with key-variable renaming, which is a bijection of type ℕ → ℕ.

def KeyRenaming : Type := ℕ → ℕ

def validKeyRenaming (r : KeyRenaming) : Prop := Function.Bijective r

-- In order to apply the renaming to an expression, we apply it to each variable.
def applyKeyRenamingP {s : Shape} (r : KeyRenaming) (e : Expression s) : Expression s :=
  match e with
  | Expression.VarK n => Expression.VarK (r n)
  | Expression.Pair e1 e2 => Expression.Pair (applyKeyRenamingP r e1) (applyKeyRenamingP r e2)
  | Expression.Perm b e1 e2 => Expression.Perm b (applyKeyRenamingP r e1) (applyKeyRenamingP r e2)
  | Expression.Enc e1 e2 => Expression.Enc (applyKeyRenamingP r e1) (applyKeyRenamingP r e2)
  | Expression.Hidden e => Expression.Hidden (applyKeyRenamingP r e)
  | e => e

-- Next, we define bit-variable, which is a bit complicated.

-- A bit renaming maps each variable `i` either to another variable `j` or to a negation of another variable `¬j`.

inductive VarOrNegVar : Type
| Var : Nat → VarOrNegVar
| NegVar : Nat → VarOrNegVar

instance : Nonempty VarOrNegVar :=
  ⟨VarOrNegVar.Var 0⟩

def BitRenaming := Nat → VarOrNegVar

-- A bit renaming is valid, if after casting it to a function ℕ → ℕ, it is a bijection.

def castVarOrNegVar (v : VarOrNegVar) : Nat :=
  match v with
  | VarOrNegVar.Var n => n
  | VarOrNegVar.NegVar n => n

def validBitRenaming (r : BitRenaming) : Prop :=
  Function.Bijective (castVarOrNegVar ∘ r)

-- Finally, we show how to apply the bit renaming to an expression.

def varOrNegVarToExpr (v : VarOrNegVar) : BitExpr :=
  match v with
  | VarOrNegVar.Var n => BitExpr.VarB n
  | VarOrNegVar.NegVar n => BitExpr.Not (BitExpr.VarB n)

def applyBitRenamingB (r : BitRenaming) (e : BitExpr) : BitExpr :=
  match e with
  | BitExpr.VarB n => varOrNegVarToExpr (r n)
  | BitExpr.Not e' => BitExpr.Not (applyBitRenamingB r e')
  | e => e

def applyBitRenaming {s : Shape} (r : BitRenaming) (p : Expression s) : Expression s :=
  match p with
  | Expression.BitE e => Expression.BitE (applyBitRenamingB r e)
  | Expression.Pair p1 p2 => Expression.Pair (applyBitRenaming r p1) (applyBitRenaming r p2)
  | Expression.Perm b p1 p2 => Expression.Perm (applyBitRenamingB r b) (applyBitRenaming r p1) (applyBitRenaming r p2)
  | Expression.Enc k e => Expression.Enc k (applyBitRenaming r e)
  | p => p

-- Finally, we are ready to define the total renaming which is a pair of bit and key renaming.

def varRenaming : Type := (BitRenaming × KeyRenaming)

def validVarRenaming (r : varRenaming) : Prop :=
  validBitRenaming r.1 ∧ validKeyRenaming r.2

def applyVarRenaming {s : Shape} (r : varRenaming) (e : Expression s) : Expression s :=
  applyKeyRenamingP r.2 (applyBitRenaming r.1 e)

-- Part iii. Adversary view

-- The goal of this section is defining adversary view, which is a function that hides
-- the parts of the expressions that are not accessible to the adversary.

-- We start by defining a function `hideEncrypted` which hides all parts of the expression
-- that cannot be decrypted using the available keys.
-- This is the function 'p' from the paper.
def hideEncrypted {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s) : Expression s :=
  match p with
  | Expression.Pair e1 e2 => Expression.Pair (hideEncrypted keys e1) (hideEncrypted keys e2)
  | Expression.Perm b e1 e2 => Expression.Perm b (hideEncrypted keys e1) (hideEncrypted keys e2)
  | Expression.Enc k e =>
    if k ∈ keys
    then Expression.Enc k (hideEncrypted keys e)
    else  Expression.Hidden k
  | p => p

-- Next, we define a function that only extracts those keys that are actually present in the expression
-- (and are are not merely used to encrypt the data)
def extractKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  match p with
  | Expression.VarK e => {Expression.VarK e}
  | Expression.Pair p1 p2 => (extractKeys p1) ∪ (extractKeys p2)
  | Expression.Perm _ p1 p2 => (extractKeys p1) ∪ (extractKeys p2)
  -- We omit the key used for encryption
  | Expression.Enc _ e => (extractKeys e)
  | Expression.Hidden _ => ∅
  | _ => ∅

-- Next, we define the 'key recovery operator (𝓕ₑ from the paper), that given a set of keys,
-- hides the encrypted parts of the expression and computes `extractKeys` from the resulting expressions.
def keyRecovery {s : Shape} (p : Expression s) (S : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  extractKeys (hideEncrypted S p)

-- In order to compute the adversary view, we need to compute the greatest fix point of the `keyRecovery`.
-- For this, we need to prove that the `keyRecovery` is monotone, i.e. if `S ⊆ T`, then `keyRecovery p S ⊆ keyRecovery p T`.

-- We start by defining an auxiliary order on the expressions,
-- based on the assertion that Hidden should be smaller than Enc.
def ExpressionInclusion :  {s : Shape} -> (p1 : Expression s) -> (p2 : Expression s) -> Bool
| .(_), Expression.BitE e1, Expression.BitE e2 => e1 == e2
| .(_), Expression.VarK e1, Expression.VarK  e2 => e1 == e2
| .(_), Expression.Pair p1 p2, Expression.Pair p1' p2' => ExpressionInclusion p1 p1' ∧ ExpressionInclusion p2 p2'
| .(_), Expression.Perm z p1 p2, Expression.Perm z' p1' p2' =>  ExpressionInclusion p1 p1' ∧ ExpressionInclusion p2 p2' ∧ ExpressionInclusion z z'
| .(_), Expression.Eps , Expression.Eps => true
| .(_), Expression.Hidden k, Expression.Hidden k' => k == k'
| .(_), Expression.Enc k e, Expression.Enc k' e' => k == k' ∧ ExpressionInclusion e e'
| .(_), Expression.Hidden k, Expression.Enc k' _ => k == k'
| .(_), _, _ => false

notation  p1 "⊆" p2 => (ExpressionInclusion p1 p2)

-- Next we introduce a block of lemmas about `ExpressionInclusion`, `hideEncrypted`, and `extractKeys`.

lemma ExpressionInclusionRfl (p : Expression s) : ExpressionInclusion p p :=
 by induction p <;>  simp [ExpressionInclusion] <;> try tauto

lemma hideEncryptedMonotone {s : Shape} (keys1 keys2 : Finset (Expression Shape.KeyS)) (p : Expression s) (h : keys1 ⊆ keys2) :
  hideEncrypted keys1 p ⊆ hideEncrypted keys2 p := by
  cases p <;> try simp [ExpressionInclusion, hideEncrypted] <;> try (constructor <;> apply hideEncryptedMonotone <;> assumption)
  case Enc s k p =>
    if hk2 : k ∈ keys2 then
      rw [if_pos hk2]
      split <;> simp [ExpressionInclusion]
      apply hideEncryptedMonotone
      assumption
    else
      rw [if_neg hk2]
      have : k ∉ keys1 := fun a => hk2 (h a)
      rw [if_neg this]
      simp [ExpressionInclusion]
  case Perm s eb e1 e2 =>
    constructor <;> try (apply hideEncryptedMonotone; assumption)
    constructor <;> try (apply hideEncryptedMonotone; assumption)
    apply ExpressionInclusionRfl

lemma keyPartsMonotone {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) : extractKeys p1 ⊆ extractKeys p2 := by
  cases p1 <;> cases p2 <;> try simp [ExpressionInclusion] at h <;> try simp [extractKeys] <;> try assumption
  case Enc.Enc sh e1 s e2 p =>
    rcases h with ⟨_, _⟩
    apply keyPartsMonotone
    assumption
  all_goals (
    rcases h with ⟨_, _⟩
    apply Finset.union_subset_union <;> apply keyPartsMonotone <;> try assumption
  )
  tauto

lemma keyRecoveryMonotone {s : Shape} (p : Expression s) (S1 S2 : Finset (Expression Shape.KeyS)) (h : S1 ⊆ S2) :
  keyRecovery p S1 ⊆ keyRecovery p S2 := by
  simp [keyRecovery]; apply keyPartsMonotone;
  apply hideEncryptedMonotone; apply h

lemma hideEncryptedSmallerValue {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s) : hideEncrypted keys p ⊆ p := by
  induction p <;> try simp [ExpressionInclusion, hideEncrypted] <;> try tauto
  case Perm s eb e1 e2 ih1 ih2 ih3 =>
    constructor; assumption
    constructor; assumption
    apply ExpressionInclusionRfl
  case Enc s ek e ih1 ih2 =>
    split <;> try simp [ExpressionInclusion, hideEncrypted]
    assumption

lemma keyRecoveryContained {s : Shape} (p : Expression s) (S : Finset (Expression Shape.KeyS)) : keyRecovery p S ⊆ (extractKeys p) := by
  apply keyPartsMonotone
  apply hideEncryptedSmallerValue

-- We are now ready to calculate the fixpoint.

def adversaryKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  greatestFixpoint (keyRecovery p) (keyRecoveryMonotone p) (extractKeys p) (keyRecoveryContained p)

lemma adversaryKeysIsFix {s : Shape} (e : Expression s) :
  let keys := adversaryKeys e
  keyRecovery e keys = keys
  := by
  apply greatestFixpointIsFixpoint

def adversaryView {s : Shape} (e : Expression s) : Expression s :=
  hideEncrypted (adversaryKeys e) e

-- To conclude, we connect parts (i), (ii), and (iii) and define symbolic indistinguishability.

def symIndistinguishable {s : Shape} (e1 e2 : Expression s) : Prop :=
  ∃ (r : varRenaming), validVarRenaming r ∧
   normalizeExpr (applyVarRenaming r (adversaryView e1)) = normalizeExpr (adversaryView e2)

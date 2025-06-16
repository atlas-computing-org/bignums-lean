
namespace Bignum

-- Predicate that checks if a string is empty or consists only of '0' characters
def allZero (s : String) : Prop :=
  s = "" ∨ s.data.all (· = '0')

-- Create a bit string of n zeros that evaluates to 0
def zeros (n : Nat) : String :=
  String.mk (List.replicate n '0')


-- Valid bit string predicate
def validBitString (s : String) : Prop :=
  s.data.all (fun c => c = '0' || c = '1') && s ≠ ""

-- Normalize bit string by removing leading zeros (except keep at least one digit)
def normalizeBitString (s : String) : String :=
  let trimmed := s.data.dropWhile (· = '0')
  String.mk (if trimmed.isEmpty then ['0'] else trimmed)


-- Convert bit string to natural number
def str2nat (s : String) : Nat :=
  s.data.foldl (fun acc c => 2 * acc + if c = '1' then 1 else 0) 0

-- Convert natural number to bit string
def nat2str (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBinary (m : Nat) : List Char :=
      if m = 0 then []
      else (if m % 2 = 1 then '1' else '0') :: toBinary (m / 2)
    String.mk (toBinary n).reverse


-- Add two bit strings representing big integers
def Add₁ (s1 s2 : String) : String :=
  let rec addBits (l1 l2 : List Char) (carry : Bool) : List Char :=
    match l1, l2 with
    | [], [] => if carry then ['1'] else []
    | [], c :: cs =>
        let sum := (if c = '1' then 1 else 0) + (if carry then 1 else 0)
        (if sum % 2 = 1 then '1' else '0') :: addBits [] cs (sum ≥ 2)
    | c :: cs, [] =>
        let sum := (if c = '1' then 1 else 0) + (if carry then 1 else 0)
        (if sum % 2 = 1 then '1' else '0') :: addBits cs [] (sum ≥ 2)
    | c1 :: cs1, c2 :: cs2 =>
        let sum := (if c1 = '1' then 1 else 0) + (if c2 = '1' then 1 else 0) + (if carry then 1 else 0)
        (if sum % 2 = 1 then '1' else '0') :: addBits cs1 cs2 (sum ≥ 2)

  let result := addBits s1.data.reverse s2.data.reverse false
  String.mk result.reverse


-- Multiply two bit strings representing big integers
def Mul₁ (s1 s2 : String) : String :=
  -- Handle special case where either input is "0"
  if s1 = "0" || s2 = "0" then "0"
  else
    let rec mulStep (acc : String) (multiplicand : String) (multiplier : List Char) : String :=
      match multiplier with
      | [] => acc
      | '0' :: rest =>
          mulStep acc (multiplicand ++ "0") rest
      | '1' :: rest =>
          let newAcc := Add₁ acc multiplicand
          mulStep newAcc (multiplicand ++ "0") rest
      | _ :: rest => mulStep acc (multiplicand ++ "0") rest  -- Should not happen with valid bit strings

    mulStep "0" s1 s2.data.reverse


-- Subtract two bit strings representing big integers (s1 >= s2)
def Sub₁ (s1 s2 : String) : String :=
  -- Handle special cases
  if s2 = "0" then s1
  else if s1 = s2 then "0"
  else
    -- Pad strings to same length with leading zeros
    let maxLen := max s1.length s2.length
    let s1Padded := (List.replicate (maxLen - s1.length) '0').asString ++ s1
    let s2Padded := (List.replicate (maxLen - s2.length) '0').asString ++ s2

    let rec subBits (l1 l2 : List Char) (borrow : Bool) : List Char :=
      match l1, l2 with
      | [], [] => []
      | c1 :: cs1, c2 :: cs2 =>
          let bit1 := if c1 = '1' then 1 else 0
          let bit2 := if c2 = '1' then 1 else 0

          let actualResult := bit1 + (if borrow then -1 else 0) - bit2
          if actualResult >= 0 then
            (if actualResult = 1 then '1' else '0') :: subBits cs1 cs2 false
          else
            -- Need to borrow from next position: current becomes actualResult + 2
            let borrowedResult := actualResult + 2
            (if borrowedResult = 1 then '1' else '0') :: subBits cs1 cs2 true
      | _, _ => [] -- Should not happen with padded strings

    let result := subBits s1Padded.data.reverse s2Padded.data.reverse false
    let reversed := result.reverse
    let trimmed := reversed.dropWhile (· = '0')
    String.mk (if trimmed.isEmpty then ['0'] else trimmed)


-- Compare two bit strings representing big integers
def compare (s1 s2 : String) : Int :=
  -- Normalize both strings to remove leading zeros
  let norm1 := normalizeBitString s1
  let norm2 := normalizeBitString s2

  -- If lengths differ after normalization, the longer one is greater
  if norm1.length < norm2.length then -1
  else if norm1.length > norm2.length then 1
  else
    -- Same length, compare lexicographically
    let rec compareChars (l1 l2 : List Char) : Int :=
      match l1, l2 with
      | [], [] => 0
      | c1 :: cs1, c2 :: cs2 =>
          if c1 < c2 then -1
          else if c1 > c2 then 1
          else compareChars cs1 cs2
      | _, _ => 0  -- Should not happen with same length strings

    compareChars norm1.data norm2.data


-- Theorem stating correctness of Add function
theorem add_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2) :
  validBitString (Add₁ s1 s2) ∧
  str2nat (Add₁ s1 s2) = str2nat s1 + str2nat s2 := by
  sorry

-- Theorem stating correctness of Mul function
theorem mul_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2) :
  validBitString (Mul₁ s1 s2) ∧
  str2nat (Mul₁ s1 s2) = str2nat s1 * str2nat s2 := by
  sorry

-- Theorem stating correctness of Sub function
theorem sub_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2)
  (h3 : str2nat s1 ≥ str2nat s2) :
  validBitString (Sub₁ s1 s2) ∧
  str2nat (Sub₁ s1 s2) = str2nat s1 - str2nat s2 := by
  sorry

-- Theorem stating correctness of zeros function
theorem zeros_correct (n : Nat) :
  (zeros n).length = n ∧
  validBitString (zeros n) ∧
  str2nat (zeros n) = 0 ∧
  allZero (zeros n) := by
  sorry

-- Theorem stating correctness of compare function
theorem compare_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2) :
  (str2nat s1 < str2nat s2 → compare s1 s2 = -1) ∧
  (str2nat s1 = str2nat s2 → compare s1 s2 = 0) ∧
  (str2nat s1 > str2nat s2 → compare s1 s2 = 1) := by
  sorry

-- Theorem stating correctness of normalizeBitString function
theorem normalizeBitString_correct (s t : String) :
  normalizeBitString s = t →
  validBitString t ∧ t.length > 0 ∧ (t.length > 1 → t.get 0 ≠ '0')
  ∧ (validBitString s → str2nat t = str2nat s) := by
  sorry

-- IgnoreInitialZeros lemma: removing leading zeros doesn't change the value
theorem IgnoreInitialZeros (s : String) (numZeros : Nat)
  (h1 : validBitString s)
  (h2 : numZeros ≤ s.length)
  (h3 : ∀ i, i < numZeros → s.data[i]? = some '0') :
  str2nat s = str2nat (s.drop numZeros) := by
  induction numZeros, h2 using Nat.le_induction with
  | base => 
    simp [String.drop_zero]
  | succ n hn ih =>
    -- n + 1 ≤ s.length, want to show str2nat s = str2nat (s.drop (n + 1))
    -- First show first character is '0'
    have first_zero : s.data[0]? = some '0' := by
      apply h3 0 (Nat.succ_pos n)
    
    -- Apply IH to s.drop 1
    have ih_hyp : ∀ i, i < n → (s.drop 1).data[i]? = some '0' := by
      intro i hi
      have orig := h3 (i + 1) (Nat.succ_lt_succ hi)
      cases h_nonempty : s.data with
      | nil => 
        simp [validBitString] at h1
      | cons c cs =>
        simp [String.drop, h_nonempty] at orig ⊢
        exact orig
    
    have s_drop1_valid : validBitString (s.drop 1) := by
      cases h_nonempty : s.data with
      | nil => 
        simp [validBitString] at h1
      | cons c cs =>
        simp [validBitString, String.drop, h_nonempty]
        constructor
        · simp [validBitString] at h1
          intro x hx
          exact h1.1 x (List.mem_cons_of_mem c hx)
        · simp
    
    have n_le_drop1 : n ≤ (s.drop 1).length := by
      simp [String.drop, String.length]
      cases h_nonempty : s.data with
      | nil => 
        simp [validBitString] at h1
      | cons c cs =>
        simp [h_nonempty]
        have : n + 1 ≤ cs.length + 1 := by
          rw [← String.length, ← h_nonempty] at hn
          exact hn
        omega
    
    have ih_applied := ih s_drop1_valid n_le_drop1 ih_hyp
    
    -- Show str2nat s = str2nat (s.drop 1) when first char is '0'
    have s_eq_drop1 : str2nat s = str2nat (s.drop 1) := by
      cases h_nonempty : s.data with
      | nil => 
        simp [validBitString] at h1
      | cons c cs =>
        have c_zero : c = '0' := by
          simp [List.get?] at first_zero
          rw [h_nonempty] at first_zero
          simp at first_zero
          exact Option.some_inj.mp first_zero
        simp [str2nat, h_nonempty, List.foldl_cons, c_zero, String.drop]
    
    -- Show (s.drop 1).drop n = s.drop (n + 1)
    have drop_assoc : (s.drop 1).drop n = s.drop (n + 1) := by
      cases h_nonempty : s.data with
      | nil => 
        simp [validBitString] at h1
      | cons c cs =>
        simp [String.drop, h_nonempty, List.drop]
    
    calc str2nat s
      = str2nat (s.drop 1) := s_eq_drop1
      _ = str2nat ((s.drop 1).drop n) := ih_applied
      _ = str2nat (s.drop (n + 1)) := by rw [drop_assoc]


end Bignum

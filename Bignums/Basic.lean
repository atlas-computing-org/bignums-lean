
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

#eval (λ a b =>
  let p := Sub₁ (nat2str a) (nat2str b)
  (str2nat p)) 150 50

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


-- Division with remainder (DivMod) function
def divMod (dividend divisor : String) : String × String :=
  -- Handle special cases
  if divisor = "0" then ("0", "0")  -- Undefined behavior, but avoid crash
  else if dividend = "0" then ("0", "0")
  else if dividend = divisor then ("1", "0")
  else if compare dividend divisor = -1 then ("0", dividend)
  else
    -- Long division algorithm for bit strings
    let rec divStep (remainder : String)
      (quotientBits : List Char) (dividendBits : List Char) : String × String :=
      match dividendBits with
      | [] =>
          let quotient := String.mk
            (if quotientBits.isEmpty then ['0'] else quotientBits.reverse)
          (quotient, remainder)
      | bit :: restBits =>
          let newRemainder :=
            if remainder = "0" then String.mk [bit] else remainder ++ String.mk [bit]
          let cmp := compare newRemainder divisor
          if cmp >= 0 then
            let subtractedRemainder := Sub₁ newRemainder divisor
            divStep subtractedRemainder ('1' :: quotientBits) restBits
          else
            divStep newRemainder ('0' :: quotientBits) restBits

    divStep "0" [] dividend.data

#eval (λ a b =>
  let p := divMod (nat2str a) (nat2str b)
  (str2nat p.1, str2nat p.2)) 15 3


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

-- Theorem stating correctness of divMod function
theorem divMod_correct (dividend divisor : String)
  (h1 : validBitString dividend) (h2 : validBitString divisor)
  (h3 : str2nat divisor > 0) :
  let (quotient, remainder) := divMod dividend divisor
  validBitString quotient ∧ validBitString remainder ∧
  str2nat quotient = str2nat dividend / str2nat divisor ∧
  str2nat remainder = str2nat dividend % str2nat divisor := by
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
  (h3 : ∀ i, i < numZeros → s.get ⟨i⟩ = some '0') :
  str2nat s = str2nat (s.drop numZeros) := by
  sorry

-- TrailingZeros lemma: trailing zeros multiply the value by powers of 2
theorem TrailingZeros (s : String) (numZeros : Nat)
  (h1 : validBitString s)
  (h2 : numZeros ≤ s.length)
  (h3 : ∀ i, s.length - numZeros ≤ i ∧ i < s.length → s.get ⟨i⟩ = some '0') :
  str2nat s = str2nat (s.take (s.length - numZeros)) * (2 ^ numZeros) := by
  sorry


-- proves that the bit string "1011" represents the decimal value 11
theorem Eleven : str2nat "1011" = 11 := by
  unfold str2nat
  simp


-- Test evaluations for divMod function
#eval divMod "1011" "10"  -- 11 ÷ 2 = 5 remainder 1 (should be ("101", "1"))
#eval divMod "1100" "11"  -- 12 ÷ 3 = 4 remainder 0 (should be ("100", "0"))
#eval divMod "1111" "100" -- 15 ÷ 4 = 3 remainder 3 (should be ("11", "11"))
#eval divMod "10000" "101" -- 16 ÷ 5 = 3 remainder 1 (should be ("11", "1"))
#eval divMod "1" "10"     -- 1 ÷ 2 = 0 remainder 1 (should be ("0", "1"))
#eval divMod "0" "10"     -- 0 ÷ 2 = 0 remainder 0 (should be ("0", "0"))
#eval divMod "101" "101"  -- 5 ÷ 5 = 1 remainder 0 (should be ("1", "0"))

-- Verify the results using str2nat
#eval str2nat "1011"  -- 11
#eval str2nat "10"    -- 2
#eval str2nat "101"   -- 5
#eval str2nat "1"     -- 1
#eval str2nat "1100"  -- 12
#eval str2nat "11"    -- 3
#eval str2nat "100"   -- 4
#eval str2nat "0"     -- 0


end Bignum

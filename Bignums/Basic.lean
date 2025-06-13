-- Valid bit string predicate
def validBitString (s : String) : Prop :=
  s.data.all (fun c => c = '0' || c = '1') && s ≠ ""

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

-- Normalize bit string by removing leading zeros (except keep at least one digit)
def normalizeBitString (s : String) : String :=
  let trimmed := s.data.dropWhile (· = '0')
  String.mk (if trimmed.isEmpty then ['0'] else trimmed)

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

-- Test subtraction
#eval! let a := "1101"  -- 13
       let b := "1010"  -- 10
       let result := Sub₁ a b
       (str2nat a, str2nat b, result, str2nat result)  -- Should be (12, 10, "10", 2)

-- Theorem stating correctness of Add function
theorem Add_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2) :
  validBitString (Add₁ s1 s2) ∧
  str2nat (Add₁ s1 s2) = str2nat s1 + str2nat s2 := by
  sorry

-- Theorem stating correctness of Mul function
theorem Mul_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2) :
  validBitString (Mul₁ s1 s2) ∧
  str2nat (Mul₁ s1 s2) = str2nat s1 * str2nat s2 := by
  sorry

-- Theorem stating correctness of Sub function
theorem Sub_correct (s1 s2 : String)
  (h1 : validBitString s1) (h2 : validBitString s2)
  (h3 : str2nat s1 ≥ str2nat s2) :
  validBitString (Sub₁ s1 s2) ∧
  str2nat (Sub₁ s1 s2) = str2nat s1 - str2nat s2 := by
  sorry

-- Theorem stating correctness of normalizeBitString function
theorem normalizeBitString_correct (s : String) :
  validBitString (normalizeBitString s) ∧
  (normalizeBitString s).length > 0 ∧
  ((normalizeBitString s).length > 1 → (normalizeBitString s).get 0 ≠ '0') ∧
  (validBitString s → str2nat (normalizeBitString s) = str2nat s) := by
  sorry

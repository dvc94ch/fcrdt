module Fcrdt.Sf

%default total

plusIdExample : (n, m : Nat) -> (n = m) -> n + n = m + m
plusIdExample n m prf = rewrite prf in Refl

plusIdExercise : (n, m, o : Nat) -> (n = m) -> (m = o) -> n + m = m + o
plusIdExercise n m o prf1 prf2 = rewrite prf1 in rewrite prf2 in Refl

mult_S_1 : (n, m : Nat) -> (m = S n) -> m * (1 + n) = m * m
mult_S_1 n m prf = rewrite prf in Refl

plus_1_neq_0 : (n : Nat) -> (n + 1) == 0 = False
plus_1_neq_0 0 = Refl
plus_1_neq_0 (S k) = Refl

andb_commutative_rhs_1 : (c : Bool) -> False = c && False
andb_commutative_rhs_1 False = Refl
andb_commutative_rhs_1 True = Refl

andb_commutative_rhs_2 : (c : Bool) -> c = c && True
andb_commutative_rhs_2 False = Refl
andb_commutative_rhs_2 True = Refl

andb_commutative : (b, c : Bool) -> b && c = c && b
andb_commutative False c = andb_commutative_rhs_1 c
andb_commutative True c = andb_commutative_rhs_2 c

andb_true_elim_2_rhs_1 : (c : Bool) -> False = True -> c = True
andb_true_elim_2_rhs_1 False prf = prf
andb_true_elim_2_rhs_1 True prf = Refl

andb_true_elim_2_rhs_2 : (c : Bool) -> c = True -> c = True
andb_true_elim_2_rhs_2 False prf = prf
andb_true_elim_2_rhs_2 True prf = prf

andb_true_elim_2 : (b, c : Bool) -> (b && c = True) -> c = True
andb_true_elim_2 False c prf = andb_true_elim_2_rhs_1 c prf
andb_true_elim_2 True c prf = andb_true_elim_2_rhs_2 c prf

zero_nbeq_plus_1 : (n : Nat) -> 0 == (n + 1) = False
zero_nbeq_plus_1 0 = Refl
zero_nbeq_plus_1 (S k) = Refl

identity_fn_applied_twice :
    (f : Bool -> Bool) ->
    ((x : Bool) -> f x = x) ->
    (b : Bool) -> f (f b) = b
identity_fn_applied_twice f prf b = rewrite prf b in rewrite prf b in Refl

andb_eq_orb : (b, c : Bool) -> (b && c = b || c) -> b = c
andb_eq_orb False c prf = prf
andb_eq_orb True c prf = rewrite prf in Refl

data Bin = BZ | B2 Bin | B2P1 Bin

incr : Bin -> Bin
incr BZ = B2P1 BZ
incr (B2 x) = B2P1 x
incr (B2P1 x) = B2 (incr x)

bin_to_nat : Bin -> Nat
bin_to_nat BZ = Z
bin_to_nat (B2 x) = (bin_to_nat x) * 2
bin_to_nat (B2P1 x) = (bin_to_nat x) * 2 + 1

test_bin_to_nat_0 : bin_to_nat (incr (incr (incr (incr BZ)))) = 4
test_bin_to_nat_0 = ?test_bin_to_nat_0_rhs

dot_op : Nat
dot_op = (bin_to_nat . incr . incr) BZ

test_bin_to_nat_1 : IO ()
test_bin_to_nat_1 = do
    (putStrLn . show . bin_to_nat . incr) BZ
    (putStrLn . show . bin_to_nat . incr . incr) BZ
    (putStrLn . show . bin_to_nat . incr . incr . incr) BZ
    (putStrLn . show . bin_to_nat . incr . incr . incr . incr) BZ
    (putStrLn . show . bin_to_nat . incr . incr . incr . incr . incr) BZ

proof_bin : (b : Bin) -> bin_to_nat (incr b) = S (bin_to_nat b)
proof_bin BZ = Refl
proof_bin (B2 x) = ?proof_bin_rhs_2
proof_bin (B2P1 x) = ?proof_bin_rhs_3

plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z 0 = Refl
plus_n_Z (S k) = let ind = plus_n_Z k in rewrite sym ind in Refl

plus_commutes_Z : (b : Nat) -> b = plus b 0
plus_commutes_Z 0 = Refl
plus_commutes_Z (S k) =
    let ind = plus_commutes_Z k in
        rewrite sym ind in Refl

plus_commutes_S : (k : Nat) -> (b : Nat) -> S (plus b k) = plus b (S k)
plus_commutes_S k 0 = Refl
plus_commutes_S k (S j) = rewrite plus_commutes_S k j in Refl

plus_commutes : (a, b : Nat) -> a + b = b + a
plus_commutes 0 b = plus_commutes_Z b
plus_commutes (S k) b =
    let ind = plus_commutes k b in
        rewrite ind in plus_commutes_S k b

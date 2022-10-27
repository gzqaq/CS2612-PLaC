Require Import Coq.ZArith.ZArith.
Local Open Scope Z.

Definition minustwo (x: Z): Z := x - 2.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f ( f ( f n ) ).

Check @doit3times.

Example prob1: 
  doit3times (fun f x => f (x + 1)) (fun x => x) 0 = 3.
Proof. reflexivity. Qed.

Check doit3times (fun (f : Z -> Z) x => f (x + 1)).

Example prob2: 
  doit3times (fun f x => f (x + 1)) minustwo 0 = 1.
Proof. reflexivity. Qed.

Example prob3:
  doit3times (fun f x => f (x + 1)) (fun x => x * x) 0 = 9.
Proof. reflexivity. Qed.

Example prob4:
  (fun f x y => f y x) Z.sub 1 2 = 1.
Proof. reflexivity. Qed.

Example prob5:
  (fun f g x => f (g x)) minustwo (fun x => x * x) 10 = 98.
Proof. reflexivity. Qed.

Example prob6:
  (fun f g x => f (g x)) (fun x => x * x) minustwo 10 = 64.
Proof. reflexivity. Qed.

Definition Func_comp {X:Type} (f:X->X) (g:X->X) (x:X) :=
  f (g x).

Definition swap {X:Type} (f:X->X->X) (x:X) (y:X) :=
  f y x.

Check doit3times swap Func_comp (fun x => x * x) minustwo 10.

Example prob7:
  doit3times swap Func_comp (fun x => x * x) minustwo 10 = 98.
Proof. reflexivity. Qed.
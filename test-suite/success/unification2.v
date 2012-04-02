(* tests to go with Grayson's patch to "destruct" for handling Univalent Foundations *)

Unset Automatic Introduction.

(* Voevodsky's original example: *)

Definition test ( X : Type ) ( x : X ) ( fxe : forall x1 : X , identity x1 x1 ) : identity ( fxe x ) ( fxe x ).
Proof. intros. destruct ( fxe x ). apply identity_refl. Defined.

(* a harder example *)

Definition UU := Type .
Inductive paths {T:Type}(t:T): T -> UU := idpath: paths t t.
Inductive foo (X0:UU) (x0:X0) : forall (X:UU)(x:X) , UU := newfoo : foo X0 x0 X0 x0.
Definition idonfoo {X0:UU} {x0:X0} {X1:UU} {x1:X1} : foo X0 x0 X1 x1 -> foo X0 x0 X1 x1.
Proof. intros * t. exact t. Defined.

Lemma hA (T:UU) (t:T) (k : foo T t T t) : paths k (idonfoo k).
Proof. intros.
   destruct k.
   unfold idonfoo.
   apply idpath.
Defined.

(* an example with two constructors *)

Inductive foo' (X0:UU) (x0:X0) : forall (X:UU)(x:X) , UU := newfoo1 : foo' X0 x0 X0 x0 | newfoo2 : foo' X0 x0 X0 x0 .
Definition idonfoo' {X0:UU} {x0:X0} {X1:UU} {x1:X1} : foo' X0 x0 X1 x1 -> foo' X0 x0 X1 x1.
Proof. intros * t. exact t. Defined.
Lemma tryb2 (T:UU) (t:T) (k : foo' T t T t) : paths k (idonfoo' k).
Proof. intros.
   destruct k.
   unfold idonfoo'. apply idpath.
   unfold idonfoo'. apply idpath.
Defined.

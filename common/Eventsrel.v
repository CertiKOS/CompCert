Require Import Valuesrel.
Require Import CKLR.
Require Export Events.

Global Instance external_call_rel R:
  Monotonic
    (@external_call)
    ([] - ==> - ==> k1 list_rel (Val.inject @@ [mi R]) ++> match_mem R ++> - ==>
     % k1 set_le (<> Val.inject @@ [mi R] * match_mem R)).
Admitted.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry_set_le_transport @external_call : typeclass_instances.

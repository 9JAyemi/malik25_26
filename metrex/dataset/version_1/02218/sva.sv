// SVA checker for mux4. Bind this to the DUT.
module mux4_sva (
  input logic A, B, C, D,
  input logic S0, S1,
  input logic X,
  // internal nets
  input logic not_S0, not_S1,
  input logic and0, and1, and2, and3,
  input logic or0, or1
);

  // convenient selects
  let selA = (~S0 & ~S1);
  let selB = (~S0 &  S1);
  let selC = ( S0 & ~S1);
  let selD = ( S0 &  S1);

  // Functional correctness (sum-of-products form, 4-state robust)
  assert property (@(A or B or C or D or S0 or S1)
                   X === ((A & selA) | (B & selB) | (C & selC) | (D & selD)))
    else $error("mux4: functional mismatch");

  // Internal structure consistency
  assert property (@(S0) not_S0 === ~S0) else $error("mux4: not_S0 incorrect");
  assert property (@(S1) not_S1 === ~S1) else $error("mux4: not_S1 incorrect");

  assert property (@(A or B or C or D or S0 or S1)
                   and0 === (A & selA) && and1 === (B & selB) &&
                   and2 === (C & selC) && and3 === (D & selD))
    else $error("mux4: and terms incorrect");

  assert property (@(A or B or C or D or S0 or S1)
                   or0 === (and0 | and1) && or1 === (and2 | and3))
    else $error("mux4: or tree incorrect");

  assert property (@(A or B or C or D or S0 or S1)
                   X === (or0 | or1))
    else $error("mux4: final OR incorrect");

  // Exactly one product term active when selects are known
  assert property (@(S0 or S1)
                   !$isunknown({S0,S1}) |-> $onehot({and0,and1,and2,and3}))
    else $error("mux4: select decode not onehot");

  // X-propagation sanity: unknown selects produce unknown X unless all data equal
  assert property (@(A or B or C or D or S0 or S1)
                   $isunknown({S0,S1}) && !(A===B && B===C && C===D) |-> $isunknown(X))
    else $error("mux4: X-propagation inconsistent");

  // Coverage: exercise all select paths and X-propagation case
  cover property (@(A or B or C or D or S0 or S1) selA ##0 (X === A));
  cover property (@(A or B or C or D or S0 or S1) selB ##0 (X === B));
  cover property (@(A or B or C or D or S0 or S1) selC ##0 (X === C));
  cover property (@(A or B or C or D or S0 or S1) selD ##0 (X === D));

  cover property (@(A or B or C or D or S0 or S1)
                  $isunknown({S0,S1}) && $isunknown(X));
endmodule

// Bind into every instance of mux4
bind mux4 mux4_sva u_mux4_sva (
  .A(A), .B(B), .C(C), .D(D),
  .S0(S0), .S1(S1),
  .X(X),
  .not_S0(not_S0), .not_S1(not_S1),
  .and0(and0), .and1(and1), .and2(and2), .and3(and3),
  .or0(or0), .or1(or1)
);
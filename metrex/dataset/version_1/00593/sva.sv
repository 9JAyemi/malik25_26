// SVA for asynch_reset_set_reg
// Bind into DUT for automatic checking

module asynch_reset_set_reg_sva (input logic D, S, R, CLK, Q, QN);

  default clocking cb @(posedge CLK); endclocking

  logic past_v;
  always_ff @(posedge CLK) past_v <= 1'b1;

  // Next-state function: reset dominates set; else capture D
  assert property (@cb disable iff (!past_v)
    Q === ( !$past(R) ? 1'b0
         : ( !$past(S) ? 1'b1 : $past(D) ) )
  ) else $error("Q next-state mismatch (R/S/D priority)");

  // Complementary output
  assert property (@cb QN === ~Q)
    else $error("QN not complement of Q");

  // Optional: changes correlate (when sampled on CLK)
  assert property (@cb $changed(Q) |-> $changed(QN))
    else $error("QN did not change with Q");
  assert property (@cb $changed(QN) |-> $changed(Q))
    else $error("Q did not change with QN");

  // Coverage
  cover property (@cb !R);                // reset asserted
  cover property (@cb R && !S);           // set asserted
  cover property (@cb R && S && D==1);    // capture 1
  cover property (@cb R && S && D==0);    // capture 0
  cover property (@cb !R && !S);          // both low (reset priority)
  cover property (@cb $rose(Q));
  cover property (@cb $fell(Q));

endmodule

bind asynch_reset_set_reg asynch_reset_set_reg_sva sva_i (.D(D), .S(S), .R(R), .CLK(CLK), .Q(Q), .QN(QN));
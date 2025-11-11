// SVA checker for mux4bit
module mux4bit_sva (input logic [3:0] A, B, input logic S, input logic [3:0] MO);

  // Functional truth table
  property p_sel0;
    @(A or B or S or MO) (S === 1'b0) |-> (MO == A);
  endproperty
  assert property (p_sel0) else $error("mux4bit: S==0 but MO!=A");

  property p_sel1;
    @(A or B or S or MO) (S === 1'b1) |-> (MO == B);
  endproperty
  assert property (p_sel1) else $error("mux4bit: S==1 but MO!=B");

  // Control must not be X/Z
  property p_ctrl_known;
    @(A or B or S or MO) !$isunknown(S);
  endproperty
  assert property (p_ctrl_known) else $error("mux4bit: S is X/Z");

  // No X/Z on MO when all inputs are known
  property p_no_x_out_when_inputs_known;
    @(A or B or S or MO) (!$isunknown({S,A,B})) |-> !$isunknown(MO);
  endproperty
  assert property (p_no_x_out_when_inputs_known)
    else $error("mux4bit: MO X/Z with known inputs");

  // Coverage: both selections exercised and handoff on S edges when A!=B
  cover property (@(A or B or S) (S===1'b0) && (MO==A));
  cover property (@(A or B or S) (S===1'b1) && (MO==B));
  cover property (@(posedge S) (A!=B) ##0 (MO==B));
  cover property (@(negedge S) (A!=B) ##0 (MO==A));

endmodule

// Bind into DUT
bind mux4bit mux4bit_sva sva_mux4bit (.A(A), .B(B), .S(S), .MO(MO));
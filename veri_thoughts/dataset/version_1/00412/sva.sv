// SVA for full_adder (binds into the DUT; checks functionality and structure, plus full truth-table coverage)
module full_adder_sva (
  input A, B, Ci,
  input S, Co,
  input w1, w2, w3
);

  // Functional correctness after delta-cycle settle
  property p_full_func;
    @(*) !$isunknown({A,B,Ci}) |-> ##0 ({Co,S} == A + B + Ci);
  endproperty
  assert property (p_full_func);

  // Gate-level consistency with internals (when inputs are known)
  property p_gate_consistency;
    @(*) !$isunknown({A,B,Ci}) |-> ##0
      (w1 == (A ^ B)) &&
      (S  == (w1 ^ Ci)) &&
      (w2 == (A & B)) &&
      (w3 == (w1 & Ci)) &&
      (Co == (w2 | w3));
  endproperty
  assert property (p_gate_consistency);

  // Outputs (and internals) never X/Z when inputs are known
  property p_no_x_out;
    @(*) !$isunknown({A,B,Ci}) |-> ##0 !$isunknown({S,Co,w1,w2,w3});
  endproperty
  assert property (p_no_x_out);

  // Full truth-table coverage (only counts when outputs are correct)
  cover property (@(*) ({A,B,Ci}==3'b000) |-> ##0 ({Co,S}==2'b00));
  cover property (@(*) ({A,B,Ci}==3'b001) |-> ##0 ({Co,S}==2'b01));
  cover property (@(*) ({A,B,Ci}==3'b010) |-> ##0 ({Co,S}==2'b01));
  cover property (@(*) ({A,B,Ci}==3'b011) |-> ##0 ({Co,S}==2'b10));
  cover property (@(*) ({A,B,Ci}==3'b100) |-> ##0 ({Co,S}==2'b01));
  cover property (@(*) ({A,B,Ci}==3'b101) |-> ##0 ({Co,S}==2'b10));
  cover property (@(*) ({A,B,Ci}==3'b110) |-> ##0 ({Co,S}==2'b10));
  cover property (@(*) ({A,B,Ci}==3'b111) |-> ##0 ({Co,S}==2'b11));

endmodule

bind full_adder full_adder_sva u_full_adder_sva (
  .A(A), .B(B), .Ci(Ci),
  .S(S), .Co(Co),
  .w1(w1), .w2(w2), .w3(w3)
);
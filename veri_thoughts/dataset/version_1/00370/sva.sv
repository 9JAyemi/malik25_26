// SVA bind file for half_full_adder hierarchy

// Half-adder checks
module sva_half_adder (input logic A,B,S,C);
  default clocking cb @($global_clock); endclocking

  // Functional checks when inputs are known; outputs not X
  assert property (!$isunknown({A,B}) |-> (S === (A ^ B) && C === (A & B)));
  assert property (!$isunknown({A,B}) |-> !$isunknown({S,C}));

  // Coverage: all input combinations
  cover property ({A,B}==2'b00);
  cover property ({A,B}==2'b01);
  cover property ({A,B}==2'b10);
  cover property ({A,B}==2'b11);
endmodule

// Full-adder checks (incl. internal structure)
module sva_full_adder (input logic A,B,C_in,S,C_out,
                       input logic H1_S,H1_C,H2_S,H2_C);
  default clocking cb @($global_clock); endclocking

  // External functional checks when inputs are known; outputs not X
  assert property (!$isunknown({A,B,C_in}) |-> (S === (A ^ B ^ C_in)));
  assert property (!$isunknown({A,B,C_in}) |-> (C_out === ((A & B) | (A & C_in) | (B & C_in))));
  assert property (!$isunknown({A,B,C_in}) |-> !$isunknown({S,C_out}));

  // Internal structure consistency
  assert property (H1_S === (A ^ B));
  assert property (H1_C === (A & B));
  assert property (H2_S === (H1_S ^ C_in));
  assert property (H2_C === (H1_S & C_in));
  assert property (S === H2_S);
  assert property (C_out === (H1_C | H2_C));

  // Coverage: all 8 input combinations + output toggles
  cover property ({A,B,C_in}==3'b000);
  cover property ({A,B,C_in}==3'b001);
  cover property ({A,B,C_in}==3'b010);
  cover property ({A,B,C_in}==3'b011);
  cover property ({A,B,C_in}==3'b100);
  cover property ({A,B,C_in}==3'b101);
  cover property ({A,B,C_in}==3'b110);
  cover property ({A,B,C_in}==3'b111);
  cover property ($rose(C_out));
  cover property ($fell(C_out));
  cover property ($rose(S));
  cover property ($fell(S));
endmodule

// Top-level composition checks (incl. internal wires)
module sva_half_full_adder (input logic A,B,C_in,S,C_out,
                            input logic H_C,F_C);
  default clocking cb @($global_clock); endclocking

  // External functional equivalence; outputs not X
  assert property (!$isunknown({A,B,C_in}) |-> (S === (A ^ B ^ C_in)));
  assert property (!$isunknown({A,B,C_in}) |-> (C_out === ((A & B) | ((A ^ B) & C_in))));
  assert property (!$isunknown({A,B,C_in}) |-> !$isunknown({S,C_out}));

  // Internal wiring and redundancy checks
  assert property (C_out === (H_C | F_C));
  assert property (H_C === (A & B));
  assert property (F_C === ((A & B) | ((A ^ B) & C_in)));

  // Coverage: all 8 input combinations
  cover property ({A,B,C_in}==3'b000);
  cover property ({A,B,C_in}==3'b001);
  cover property ({A,B,C_in}==3'b010);
  cover property ({A,B,C_in}==3'b011);
  cover property ({A,B,C_in}==3'b100);
  cover property ({A,B,C_in}==3'b101);
  cover property ({A,B,C_in}==3'b110);
  cover property ({A,B,C_in}==3'b111);
endmodule

// Bind assertions to DUT hierarchy
bind half_adder      sva_half_adder      HA_SVA (.*);
bind full_adder      sva_full_adder      FA_SVA (.A(A),.B(B),.C_in(C_in),.S(S),.C_out(C_out),
                                                .H1_S(H1_S),.H1_C(H1_C),.H2_S(H2_S),.H2_C(H2_C));
bind half_full_adder sva_half_full_adder HFA_SVA(.A(A),.B(B),.C_in(C_in),.S(S),.C_out(C_out),
                                                 .H_C(H_C),.F_C(F_C));
// SVA for top_module — concise, high-quality checks and coverage
// Bindable checker module plus bind statement

`ifndef SYNTHESIS
module top_module_sva (
  input  logic       A,
  input  logic       B,
  input  logic       C_in,
  input  logic [1:0] fa1_out,
  input  logic [1:0] fa2_out,
  input  logic       parity_bit,
  input  logic [8:0] out
);
  // Fire assertions on any combinational change
  event comb_change;
  always @* -> comb_change;

  // Helper: inputs known
  let KI = !$isunknown({A,B,C_in});

  // No X/Z on internal/outputs when inputs are known
  ap_no_x: assert property (@(comb_change) KI |-> ##0 !$isunknown({fa1_out,fa2_out,parity_bit,out}));

  // Full-adder 1 functionality
  ap_fa1_sum : assert property (@(comb_change) KI |-> ##0 (fa1_out[0] == (A ^ B ^ C_in)));
  ap_fa1_cout: assert property (@(comb_change) KI |-> ##0 (fa1_out[1] == ((A & B) | (C_in & (A ^ B)))));

  // Full-adder 2 functionality (C_in fixed to 0)
  ap_fa2_sum : assert property (@(comb_change) KI |-> ##0 (fa2_out[0] == (fa1_out[0] ^ fa1_out[1])));
  ap_fa2_cout: assert property (@(comb_change) KI |-> ##0 (fa2_out[1] == (fa1_out[0] & fa1_out[1])));

  // Parity bit functionality (redundant AND|XOR simplifies to XOR)
  ap_parity_expr: assert property (@(comb_change) KI |-> ##0 (parity_bit == ((A ^ B ^ fa2_out[0]) & (A | B | fa2_out[0]))));
  ap_parity_xor : assert property (@(comb_change) KI |-> ##0 (parity_bit == (A ^ B ^ fa2_out[0])));

  // Output packing and zero-extension to 9 bits
  ap_out_pack_low : assert property (@(comb_change) KI |-> ##0 (out[2:0] == {parity_bit, fa2_out}));
  ap_out_high_zero: assert property (@(comb_change) KI |-> ##0 (out[8:3] == '0));

  // Functional coverage
  // All 8 input combinations
  cv_inputs_000: cover property (@(comb_change) {A,B,C_in} == 3'b000);
  cv_inputs_001: cover property (@(comb_change) {A,B,C_in} == 3'b001);
  cv_inputs_010: cover property (@(comb_change) {A,B,C_in} == 3'b010);
  cv_inputs_011: cover property (@(comb_change) {A,B,C_in} == 3'b011);
  cv_inputs_100: cover property (@(comb_change) {A,B,C_in} == 3'b100);
  cv_inputs_101: cover property (@(comb_change) {A,B,C_in} == 3'b101);
  cv_inputs_110: cover property (@(comb_change) {A,B,C_in} == 3'b110);
  cv_inputs_111: cover property (@(comb_change) {A,B,C_in} == 3'b111);

  // All realizable fa2_out combinations (00,01,10)
  cv_fa2_00: cover property (@(comb_change) KI && (fa2_out == 2'b00));
  cv_fa2_01: cover property (@(comb_change) KI && (fa2_out == 2'b01));
  cv_fa2_10: cover property (@(comb_change) KI && (fa2_out == 2'b10));

  // Parity both values and toggling
  cv_parity0: cover property (@(comb_change) KI && (parity_bit == 1'b0));
  cv_parity1: cover property (@(comb_change) KI && (parity_bit == 1'b1));
  cv_parity_toggle_up  : cover property (@(comb_change) KI && (parity_bit==0) ##1 (parity_bit==1));
  cv_parity_toggle_down: cover property (@(comb_change) KI && (parity_bit==1) ##1 (parity_bit==0));
endmodule

// Bind into DUT (accesses internal nets)
bind top_module top_module_sva u_top_module_sva (
  .A(A),
  .B(B),
  .C_in(C_in),
  .fa1_out(fa1_out),
  .fa2_out(fa2_out),
  .parity_bit(parity_bit),
  .out(out)
);
`endif
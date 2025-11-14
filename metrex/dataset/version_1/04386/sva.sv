// SVA: bindable checker for top_module
// Focus: functional correctness, connectivity, onehot behavior, X-propagation protection, and basic coverage.
// Synthesis off
`ifndef TOP_MODULE_SVA
`define TOP_MODULE_SVA

module top_module_asserts
(
  input  logic       a,
  input  logic       b,
  input  logic       c,
  input  logic       w,
  input  logic       x,
  input  logic       y,
  input  logic       z,
  input  logic       nor_out,
  input  logic [3:0] decoder_out,
  input  logic       final_out
);

  default clocking cb @(a or b or c or w or x or y or z or nor_out or decoder_out or final_out); endclocking

  // Knownness: if inputs are known, all derived signals must be known
  assert property (!$isunknown({a,b,c}) |-> !$isunknown({nor_out,decoder_out,w,x,y,z,final_out}));

  // NOR gate truth (note: this will flag if NOR is implemented incorrectly)
  assert property (!$isunknown({a,b}) |-> (nor_out == ~(a | b)));

  // Decoder equations
  assert property (!$isunknown({a,b,c}) |-> (decoder_out[0] == ~(a | b |  c)));
  assert property (!$isunknown({a,b,c}) |-> (decoder_out[1] == ~(a | b | ~c)));
  assert property (!$isunknown({a,b,c}) |-> (decoder_out[2] == ~(a | ~b |  c)));
  assert property (!$isunknown({a,b,c}) |-> (decoder_out[3] == ~(a | ~b | ~c)));

  // Top-level output connectivity to decoder_out
  assert property ({w,x,y,z} == decoder_out);

  // Decoder one-hot-or-zero behavior
  assert property ($onehot0({w,x,y,z}));

  // Functional module width/truncation effect: final_out equals nor_out AND LSB of decoder_out
  assert property (final_out == (nor_out & decoder_out[0]));

  // Functional relationships (redundant cross-checks using top outputs)
  assert property (w == ~(a | b |  c));
  assert property (x == ~(a | b | ~c));
  assert property (y == ~(a | ~b |  c));
  assert property (z == ~(a | ~b | ~c));

  // Coverage: all input combinations observed
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b000);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b001);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b010);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b011);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b100);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b101);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b110);
  cover property (!\$isunknown({a,b,c}) && {a,b,c} == 3'b111);

  // Coverage: each decoder output asserted at least once, and final_out asserted
  cover property (w);
  cover property (x);
  cover property (y);
  cover property (z);
  cover property (final_out);

  // Coverage: NOR both polarities
  cover property (nor_out);
  cover property (!nor_out);

endmodule

// Bind into DUT
bind top_module top_module_asserts tma (
  .a(a), .b(b), .c(c),
  .w(w), .x(x), .y(y), .z(z),
  .nor_out(nor_out),
  .decoder_out(decoder_out),
  .final_out(final_out)
);

`endif
// Synthesis on
// SVA for comparator_4bit
module comparator_4bit_sva (
  input logic        clk,
  input logic [3:0]  in0, in1,
  input logic [3:0]  in0_reg, in1_reg,
  input logic [1:0]  stage,
  input logic        EQ, GT
);

  default clocking cb @(posedge clk); endclocking

  // Stage sequencing (00->01->10->11->00)
  assert property (!$isunknown($past(stage)) |-> stage == (($past(stage)==2'b11) ? 2'b00 : ($past(stage)+2'b01)));

  // Capture when stage==00
  assert property (stage==2'b00 |-> (in0_reg==in0 && in1_reg==in1));
  // Hold when stage!=00
  assert property (stage inside {2'b01,2'b10,2'b11} |-> $stable(in0_reg) && $stable(in1_reg));
  // Next-cycle sampled hold after 00->01 boundary
  assert property ($past(stage)==2'b00 && stage==2'b01 |-> (in0_reg==$past(in0) && in1_reg==$past(in1)));
  // Regs only change at stage==00
  assert property ($changed(in0_reg) |-> stage==2'b00);
  assert property ($changed(in1_reg) |-> stage==2'b00);

  // Output correctness and consistency
  assert property (!$isunknown({in0_reg,in1_reg}) |-> EQ == (in0_reg==in1_reg));
  assert property (!$isunknown({in0_reg,in1_reg}) |-> GT == (in0_reg>in1_reg));
  assert property (!(EQ && GT));                         // mutual exclusion
  assert property ($changed({EQ,GT}) |-> $changed({in0_reg,in1_reg}));
  assert property (!$isunknown({in0_reg,in1_reg}) |-> !$isunknown({EQ,GT}));

  // Functional coverage
  cover property (stage==2'b00 ##1 stage==2'b01 ##1 stage==2'b10 ##1 stage==2'b11 ##1 stage==2'b00);
  cover property (!$isunknown({in0_reg,in1_reg}) && (in0_reg==in1_reg) &&  EQ && !GT);
  cover property (!$isunknown({in0_reg,in1_reg}) && (in0_reg> in1_reg) && !EQ &&  GT);
  cover property (!$isunknown({in0_reg,in1_reg}) && (in0_reg< in1_reg) && !EQ && !GT);

endmodule

bind comparator_4bit comparator_4bit_sva sva_i(.*);
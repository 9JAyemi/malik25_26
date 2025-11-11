// SVA for Test: checks registered add with 7-bit truncation and key corner cases

module Test_sva (
  input  logic        clk,
  input  logic [7:0]  operand_a,
  input  logic [7:0]  operand_b,
  input  logic [6:0]  out
);
  // establish past-valid after first clock
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Functional correctness: out is lower 7 bits of previous-cycle sum
  ap_sum_mod128: assert property (
    past_valid && !$isunknown($past({operand_a,operand_b}))
    |-> out == ($past(operand_a) + $past(operand_b))[6:0]
  );

  // Stability: if inputs don’t change, output holds value
  ap_hold_when_inputs_stable: assert property (
    past_valid && $stable({operand_a,operand_b})
    |-> out == $past(out)
  );

  // No X/Z on output after warm-up
  ap_no_x_out: assert property (
    past_valid |-> !$isunknown(out)
  );

  // Coverage: no-overflow case (sum < 128)
  cp_no_overflow: cover property (
    past_valid && !$isunknown($past({operand_a,operand_b})) &&
    ($past(operand_a)+$past(operand_b)) < 9'd128 &&
    out == ($past(operand_a)+$past(operand_b))[6:0]
  );

  // Coverage: overflow case (sum >= 128)
  cp_overflow: cover property (
    past_valid && !$isunknown($past({operand_a,operand_b})) &&
    ($past(operand_a)+$past(operand_b)) >= 9'd128 &&
    out == ($past(operand_a)+$past(operand_b))[6:0]
  );

  // Coverage: key corners
  cp_zero_zero: cover property (
    past_valid && $past(operand_a)==8'h00 && $past(operand_b)==8'h00 && out==7'h00
  );

  cp_boundary_wrap: cover property (
    past_valid && $past(operand_a)==8'h7F && $past(operand_b)==8'h01 && out==7'h00
  );

  cp_max_max: cover property (
    past_valid && $past(operand_a)==8'hFF && $past(operand_b)==8'hFF && out==7'h7E
  );
endmodule

bind Test Test_sva u_test_sva (
  .clk(clk),
  .operand_a(operand_a),
  .operand_b(operand_b),
  .out(out)
);
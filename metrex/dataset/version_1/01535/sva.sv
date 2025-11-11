// SVA for adder_comparator
// Focused, high-quality checks and coverage

module adder_comparator_sva
(
  input logic        clk,
  input logic        reset,
  input logic [3:0]  input1,
  input logic [3:0]  input2,
  input logic [3:0]  sum,
  input logic [1:0]  comparison_result,
  input logic [3:0]  adder_output
);

  // Helper: expected comparison encoding from adder_output[3:2]
  function automatic logic [1:0] comp_expected(input logic [3:0] aout);
    if (aout[3:2] > 2'b10)      comp_expected = 2'b10; // greater than
    else if (aout[3:2] == 2'b10) comp_expected = 2'b01; // equal to
    else                         comp_expected = 2'b00; // less than
  endfunction

  // Reset behavior: internal/output regs under reset
  assert property (@(posedge clk)
    reset |-> (adder_output == 4'b0 && comparison_result == 2'b0 && $stable(sum)));

  // Registered adder: truncation to 4 LSBs as implemented
  assert property (@(posedge clk) disable iff (reset)
    adder_output == $past((input1 + input2)[3:0]));

  // Pipeline: sum is 1-cycle delayed adder_output
  assert property (@(posedge clk) disable iff (reset)
    sum == $past(adder_output));

  // Comparator mapping is exact and single-cycle with adder_output
  assert property (@(posedge clk) disable iff (reset)
    comparison_result == comp_expected(adder_output));

  // Comparator never outputs 2'b11
  assert property (@(posedge clk) disable iff (reset)
    comparison_result != 2'b11);

  // No X/Z on key regs when not in reset
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({adder_output, sum, comparison_result}));

  // Functional coverage: exercise all comparator outcomes
  cover property (@(posedge clk) disable iff (reset)
    (adder_output[3:2] <  2'b10) && (comparison_result == 2'b00));
  cover property (@(posedge clk) disable iff (reset)
    (adder_output[3:2] == 2'b10) && (comparison_result == 2'b01));
  cover property (@(posedge clk) disable iff (reset)
    (adder_output[3:2] >  2'b10) && (comparison_result == 2'b10));

  // Coverage: observe the pipeline handoff from adder_output to sum
  cover property (@(posedge clk) disable iff (reset)
    $changed(adder_output) ##1 (sum == $past(adder_output)));

  // Coverage: post-reset behavior and first valid sum
  cover property (@(posedge clk) $fell(reset) ##1 (sum == 4'h0));

endmodule

// Bind into DUT (tools supporting bind)
bind adder_comparator adder_comparator_sva sva_i (
  .clk                (clk),
  .reset              (reset),
  .input1             (input1),
  .input2             (input2),
  .sum                (sum),
  .comparison_result  (comparison_result),
  .adder_output       (adder_output)
);
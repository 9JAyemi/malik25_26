module top_module_sva (
  input logic clk,
  input logic reset,
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic select,
  input logic [7:0] out
);

  // Reset drives the registered output to zero on the next cycle.
  check_reset_forces_zero: assert property (
    @(posedge clk) reset |=> (out == 8'd0)
  );

  // With select high, output matches the previous cycle's 8-bit sum.
  check_select_high_result: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (select && !$past(reset)) |-> (out == ($past(in1) + $past(in2)))
  );

  // With select low, output matches the previous cycle's 8-bit sum.
  check_select_low_result: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (!select && !$past(reset)) |-> (out == ($past(in1) + $past(in2)))
  );

  // Adding zero on in2 passes through in1.
  check_in2_zero_passthrough: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (!$past(reset) && ($past(in2) == 8'd0)) |-> (out == $past(in1))
  );

  // Adding zero on in1 passes through in2.
  check_in1_zero_passthrough: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (!$past(reset) && ($past(in1) == 8'd0)) |-> (out == $past(in2))
  );

  // Equal operands produce an even sum.
  check_equal_operands_even_sum: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (!$past(reset) && ($past(in1) == $past(in2))) |-> (out[0] == 1'b0)
  );

  // 8-bit addition wraps on overflow.
  check_overflow_wrap_to_zero: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (!$past(reset) && ($past(in1) == 8'hFF) && ($past(in2) == 8'h01)) |-> (out == 8'h00)
  );

  // Max plus max produces 8'hFE.
  check_max_plus_max: assert property (
    @(posedge clk) disable iff (reset || $initstate)
    (!$past(reset) && ($past(in1) == 8'hFF) && ($past(in2) == 8'hFF)) |-> (out == 8'hFE)
  );

endmodule
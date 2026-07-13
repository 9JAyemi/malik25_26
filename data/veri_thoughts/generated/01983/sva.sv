module mult_system_sva (
  input logic clk,
  input logic reset,
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [15:0] out,
  input logic [7:0] out_lo
);

  // When reset is asserted, out must be zero in the same cycle.
  reset_forces_out_zero: assert property (
    @(posedge clk) reset |-> (out == 16'd0)
  );

  // When active and previous cycle not in reset, out equals last cycle's product.
  out_matches_prev_product_when_no_reset: assert property (
    @(posedge clk) disable iff (reset) !$past(reset) |-> (out == ($past(in1) * $past(in2)))
  );

  // When active and previous cycle was in reset, out must be zero (captures 0 from mult_result).
  out_zero_if_prev_cycle_in_reset: assert property (
    @(posedge clk) disable iff (reset) $past(reset) |-> (out == 16'd0)
  );

  // When active, out_lo must equal the lower byte of out.
  out_lo_matches_out_lsb_when_active: assert property (
    @(posedge clk) disable iff (reset) (out_lo == out[7:0])
  );

  // When active and previous cycle not in reset, out_lo equals lower byte of last cycle's product.
  out_lo_matches_prev_product_lsb: assert property (
    @(posedge clk) disable iff (reset) !$past(reset) |-> (out_lo == (($past(in1) * $past(in2))[7:0]))
  );

  // When active and previous cycle was in reset, out_lo must be zero (lower byte of zero).
  out_lo_zero_if_prev_cycle_in_reset: assert property (
    @(posedge clk) disable iff (reset) $past(reset) |-> (out_lo == 8'd0)
  );

  // When active and previous cycle in1 was 1, out equals in2 with zero-extended upper byte.
  out_eq_in2_when_mul_by_one_on_in1: assert property (
    @(posedge clk) disable iff (reset)
      (!$past(reset) && ($past(in1) == 8'd1)) |-> ((out[7:0] == $past(in2)) && (out[15:8] == 8'd0))
  );

  // When active and previous cycle in2 was 1, out equals in1 with zero-extended upper byte.
  out_eq_in1_when_mul_by_one_on_in2: assert property (
    @(posedge clk) disable iff (reset)
      (!$past(reset) && ($past(in2) == 8'd1)) |-> ((out[7:0] == $past(in1)) && (out[15:8] == 8'd0))
  );

  // When active and any previous multiplicand was zero, out must be zero.
  out_zero_when_either_operand_prev_zero: assert property (
    @(posedge clk) disable iff (reset)
      (!$past(reset) && (($past(in1) == 8'd0) || ($past(in2) == 8'd0))) |-> (out == 16'd0)
  );

  // When active and both previous inputs were 8'hFF, out must be 16'hFE01 (255*255).
  out_equals_255x255_when_prev_inputs_ff: assert property (
    @(posedge clk) disable iff (reset)
      (!$past(reset) && ($past(in1) == 8'hFF) && ($past(in2) == 8'hFF)) |-> (out == 16'hFE01)
  );

endmodule
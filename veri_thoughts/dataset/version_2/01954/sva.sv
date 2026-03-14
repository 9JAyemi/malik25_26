module swap_first_last_16_bits_sva (
  input logic clk,
  input logic reset,
  input logic [31:0] in_vec,
  input logic control,
  input logic [31:0] out_vec
);

  // While reset is HIGH, out_vec must be zero.
  reset_clears_outvec: assert property (
    @(posedge clk) reset |-> (out_vec == 32'd0)
  );

  // Next-cycle out_vec equals previous in_vec or its 16-bit-swapped version based on previous control.
  deterministic_next_state: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |=> (out_vec == ($past(control) ? {$past(in_vec[15:0]), $past(in_vec[31:16])} : $past(in_vec)))
  );

  // Next-cycle upper 16 bits reflect previous control selection (swap or passthrough).
  next_upper_half_function: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |=> (out_vec[31:16] == ($past(control) ? $past(in_vec[15:0]) : $past(in_vec[31:16])))
  );

  // Next-cycle lower 16 bits reflect previous control selection (swap or passthrough).
  next_lower_half_function: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |=> (out_vec[15:0] == ($past(control) ? $past(in_vec[31:16]) : $past(in_vec[15:0])))
  );

  // If control is LOW, next-cycle out_vec passes through previous in_vec.
  passthrough_when_control0: assert property (
    @(posedge clk) disable iff (reset)
      (!control) |=> (out_vec == $past(in_vec))
  );

  // If control is HIGH, next-cycle out_vec swaps previous in_vec upper/lower 16 bits.
  swap_when_control1: assert property (
    @(posedge clk) disable iff (reset)
      (control) |=> ((out_vec[31:16] == $past(in_vec[15:0])) && (out_vec[15:0] == $past(in_vec[31:16])))
  );

endmodule
module pipeline_register_sva #(
  parameter n = 8
) (
  input logic clk,
  input logic rst,
  input logic [n-1:0] in,
  input logic [n-1:0] out
);

  // Reset forces the register output to zero.
  check_reset_forces_zero: assert property (
    @(posedge clk) rst |-> (out == '0)
  );

  // Continuous reset keeps the sampled output zero and unchanged.
  check_reset_holds_zero: assert property (
    @(posedge clk) ($past(rst) && rst) |-> ($stable(out) && (out == '0))
  );

  // The first non-reset clock still samples the reset value before loading input.
  check_first_clock_after_reset_samples_zero: assert property (
    @(posedge clk) disable iff (rst) $past(rst) |-> ($stable(out) && (out == '0))
  );

endmodule
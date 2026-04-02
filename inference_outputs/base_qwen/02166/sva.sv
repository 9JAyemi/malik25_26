module accumulator_sva (
  input logic clk,
  input logic rst,
  input logic [7:0] data_in,
  output logic [7:0] out
);

  // Reset behavior: sum should be 0 at reset
  reset: assert property (
    @(posedge clk) disable iff (!rst) (sum == 8'b0)
  );

  // Sequential logic: sum should update on each positive edge of clk
  sequential_update: assert property (
    @(posedge clk) disable iff (!rst) (sum == sum + data_in)
  );

  // Output should always reflect the current sum
  output_update: assert property (
    @(posedge clk) disable iff (!rst) (out == sum)
  );

endmodule
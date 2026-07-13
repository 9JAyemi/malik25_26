module simple_counter_sva (
  input logic clk,
  input logic rst,
  input logic en,
  input logic [31:0] count
);

  // Reset behavior: count should be 0 at reset
  reset_behavior: assert property (
    @(posedge clk) disable iff (!rst) count == 32'b0
  );

  // Enable behavior: count should increment when en is high
  enable_behavior: assert property (
    @(posedge clk) disable iff (!rst) (en == 1'b1) |-> count == count + 1
  );

  // Disable behavior: count should not increment when en is low
  disable_behavior: assert property (
    @(posedge clk) disable iff (!rst) (en == 1'b0) |-> count == count
  );

endmodule
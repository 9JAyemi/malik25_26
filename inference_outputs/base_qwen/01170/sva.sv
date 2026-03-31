```systemverilog
module binary_counter_sva (
  input logic clk,
  input logic rst,
  output logic [3:0] count
);
  // Reset behavior: count should be 0 after reset
  reset_behavior: assert property (
    @(posedge clk) disable iff (!rst) count == 4'b0000
  );

  // Counting behavior: count should increment by 1 on each clock edge
  counting_behavior: assert property (
    @(posedge clk) disable iff (!rst) count == count + 1
  );
endmodule
```
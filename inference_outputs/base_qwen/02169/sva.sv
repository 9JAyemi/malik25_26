module arithmetic_op_sva (
   input logic clk,
   input logic rst_n,
   input logic [7:0] a,
   input logic [7:0] b,
   input logic [1:0] ctrl,
   input logic [7:0] result
);

   // Combinational logic, so use @(posedge clk)
   // Check that the result is correctly calculated based on the control signal
   check_result: assert property (
      @(posedge clk) disable iff (!rst_n) (ctrl == 2'b00) |-> (result == a + b)
   );
   check_result_sub: assert property (
      @(posedge clk) disable iff (!rst_n) (ctrl == 2'b01) |-> (result == a - b)
   );
   check_result_xor: assert property (
      @(posedge clk) disable iff (!rst_n) (ctrl == 2'b10) |-> (result == a ^ b)
   );
   check_result_default: assert property (
      @(posedge clk) disable iff (!rst_n) (ctrl != 2'b00 && ctrl != 2'b01 && ctrl != 2'b10) |-> (result == 8'b0)
   );

   // Check that the result is not driven during reset
   check_result_reset: assert property (
      @(posedge clk) disable iff (rst_n) (result != 8'b0)
   );

endmodule
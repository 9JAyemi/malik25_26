```systemverilog
module priority_encoder_sva #(
  parameter n=4,
  parameter m=2
) (
  input [n-1:0] in,
  output [m-1:0] out
);

  // Combinational logic, so use @(posedge clk)
  // No clock or reset signals are present in the RTL

  // The priority encoder outputs the binary code of the highest priority input signal
  // The highest priority input signal is determined by the position of the first '1' from the left
  // If no input signals are high, the output is 2'b00

  // Check that the output is correct for each possible input
  // Highest priority input signal is in[3]
  priority_3: assert property (
    @(posedge clk) disable iff (1'b0) (in == 4'b1110) |-> (out == 2'b00)
  );
  // Highest priority input signal is in[2]
  priority_2: assert property (
    @(posedge clk) disable iff (1'b0) (in == 4'b1101) |-> (out == 2'b01)
  );
  // Highest priority input signal is in[1]
  priority_1: assert property (
    @(posedge clk) disable iff (1'b0) (in == 4'b1011) |-> (out == 2'b10)
  );
  // Highest priority input signal is in[0]
  priority_0: assert property (
    @(posedge clk) disable iff (1'b0) (in == 4'b0111) |-> (out == 2'b11)
  );
  // Default output if no input signals are high
  default_out: assert property (
    @(posedge clk) disable iff (1'b0) (in == 4'b0000) |-> (out == 2'b00)
  );

endmodule
```
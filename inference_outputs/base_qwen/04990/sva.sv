```systemverilog
module ripple_carry_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic cin,
  output logic [3:0] sum,
  output logic cout
);

  // Full adder logic is combinational, but we will use @(posedge clk) for assertions.

  // Sum calculation is correct for each bit position
  sum_calculation: assert property (
    @(posedge clk) disable iff (!cin) (sum[0] == A[0] ^ B[0] ^ cin) &&
    @(posedge clk) disable iff (!cin) (sum[1] == A[1] ^ B[1] ^ carry[0]) &&
    @(posedge clk) disable iff (!cin) (sum[2] == A[2] ^ B[2] ^ carry[1]) &&
    @(posedge clk) disable iff (!cin) (sum[3] == A[3] ^ B[3] ^ carry[2])
  );

  // Carry calculation is correct for each bit position
  carry_calculation: assert property (
    @(posedge clk) disable iff (!cin) (carry[0] == (A[0] & B[0]) | (A[0] & cin) | (B[0] & cin)) &&
    @(posedge clk) disable iff (!cin) (carry[1] == (A[1] & B[1]) | (A[1] & carry[0]) | (B[1] & carry[0])) &&
    @(posedge clk) disable iff (!cin) (carry[2] == (A[2] & B[2]) | (A[2] & carry[1]) | (B[2] & carry[1])) &&
    @(posedge clk) disable iff (!cin) (cout == (A[3] & B[3]) | (A[3] & carry[2]) | (B[3] & carry[2]))
  );

endmodule
```
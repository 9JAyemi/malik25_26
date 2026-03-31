```systemverilog
module adder4bit_sva (
  input logic clk,
  input logic [3:0] a,
  input logic [3:0] b,
  input logic cin,
  input logic cout,
  output logic [3:0] sum
);

  // Full adder for the least significant bit
  full_adder fa0 (
    .a(a[0]),
    .b(b[0]),
    .cin(cin),
    .sum(sum[0]),
    .cout(cout)
  );

  // Full adder for the second least significant bit
  full_adder fa1 (
    .a(a[1]),
    .b(b[1]),
    .cin(cout),
    .sum(sum[1]),
    .cout(cout)
  );

  // Full adder for the third least significant bit
  full_adder fa2 (
    .a(a[2]),
    .b(b[2]),
    .cin(cout),
    .sum(sum[2]),
    .cout(cout)
  );

  // Full adder for the most significant bit
  full_adder fa3 (
    .a(a[3]),
    .b(b[3]),
    .cin(cout),
    .sum(sum[3]),
    .cout(cout)
  );

  // Combinational logic, so use @(posedge clk)
  // Sum should be the result of a + b + cin
  sum_check: assert property (
    @(posedge clk) disable iff (!clk) sum == a + b + cin
  );

  // Carry out should be the carry from the most significant bit
  carry_out_check: assert property (
    @(posedge clk) disable iff (!clk) cout == (a[3] & b[3] & cin) | (a[3] & b[3]) | (a[3] & cin) | (b[3] & cin)
  );

endmodule
```
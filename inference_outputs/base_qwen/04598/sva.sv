```systemverilog
module adder4_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic cin,
  input logic [3:0] sum,
  input logic cout
);

  // Combinational logic: sum and cout are determined by a, b, and cin
  // Clocked assertions are used to ensure the logic is correct at each clock edge

  // First stage of addition
  property p_fa1;
    @(posedge clk) disable iff (!rst_n) sum[0] == a[0] ^ b[0] ^ cin;
  endproperty
  assert property (p_fa1) else $error("First stage addition error");

  // Second stage of addition
  property p_fa2;
    @(posedge clk) disable iff (!rst_n) sum[1] == a[1] ^ b[1] ^ cin;
  endproperty
  assert property (p_fa2) else $error("Second stage addition error");

  // Third stage of addition
  property p_fa3;
    @(posedge clk) disable iff (!rst_n) sum[2] == a[2] ^ b[2] ^ cin;
  endproperty
  assert property (p_fa3) else $error("Third stage addition error");

  // Fourth stage of addition
  property p_fa4;
    @(posedge clk) disable iff (!rst_n) sum[3] == a[3] ^ b[3] ^ cin;
  endproperty
  assert property (p_fa4) else $error("Fourth stage addition error");

  // Carry out calculation
  property p_cout;
    @(posedge clk) disable iff (!rst_n) cout == (a[0] & b[0]) | (cin & a[0]) | (cin & b[0]);
  endproperty
  assert property (p_cout) else $error("Carry out calculation error");

endmodule
```
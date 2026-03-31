```systemverilog
module calculator_sva (
  input signed [7:0] a,
  input signed [7:0] b,
  input op,
  input clk,
  output reg signed [7:0] result,
  output reg overflow
);

  // Combinational logic for result calculation
  // result = a + b if op == 0, result = a - b if op == 1
  comb_result: assert property (
    @(posedge clk) disable iff (!clk) (op == 0) |-> (result == a + b)
  );
  comb_result_neg: assert property (
    @(posedge clk) disable iff (!clk) (op == 1) |-> (result == a - b)
  );

  // Sequential logic for overflow detection
  // Overflow or underflow condition
  seq_overflow: assert property (
    @(posedge clk) disable iff (!clk) 
      ((result[7] == 1 && op == 0 && a[7] == 1 && b[7] == 1) ||
       (result[7] == 1 && op == 1 && a[7] == 0 && b[7] == 1) ||
       (result[7] == 0 && op == 1 && a[7] == 1 && b[7] == 0)) |-> (overflow == 1'b1)
  );
  seq_no_overflow: assert property (
    @(posedge clk) disable iff (!clk) 
      !((result[7] == 1 && op == 0 && a[7] == 1 && b[7] == 1) ||
        (result[7] == 1 && op == 1 && a[7] == 0 && b[7] == 1) ||
        (result[7] == 0 && op == 1 && a[7] == 1 && b[7] == 0)) |-> (overflow == 1'b0)
  );

endmodule
```
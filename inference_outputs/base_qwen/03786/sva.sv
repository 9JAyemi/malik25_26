```systemverilog
module comparator_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic EQ,
  input logic GT
);
  // EQ is HIGH when A is equal to B
  eq_check: assert property (
    @(posedge clk) disable iff (!RESETn) (A == B) |-> (EQ == 1'b1)
  );
  
  // GT is HIGH when A is greater than B
  gt_check: assert property (
    @(posedge clk) disable iff (!RESETn) (A > B) |-> (GT == 1'b1)
  );
  
  // EQ is LOW when A is not equal to B
  eq_not_check: assert property (
    @(posedge clk) disable iff (!RESETn) (A != B) |-> (EQ == 1'b0)
  );
  
  // GT is LOW when A is not greater than B
  gt_not_check: assert property (
    @(posedge clk) disable iff (!RESETn) (A <= B) |-> (GT == 1'b0)
  );
endmodule
```
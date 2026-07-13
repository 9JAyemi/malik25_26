module bitwise_and_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] result
);

  // Combinational logic: result is the bitwise AND of a and b
  comb_logic: assert property (
    @(posedge clk) disable iff (!reset_n) (result == (a & b))
  );

endmodule
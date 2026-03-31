```systemverilog
module sync_up_down_counter_sva (
  input logic clk,
  input logic up_down,
  input logic [2:0] q
);

  ///// Counter behavior /////
  // Counter increments when up_down is 0 and q is not 7.
  counter_inc: assert property (
    @(posedge clk) disable iff (!clk) (up_down == 0 && q != 7) |-> q == q + 1
  );
  // Counter decrements when up_down is 1 and q is not 0.
  counter_dec: assert property (
    @(posedge clk) disable iff (!clk) (up_down == 1 && q != 0) |-> q == q - 1
  );
  // Counter wraps around to 0 when up_down is 0 and q is 7.
  counter_wrap_up: assert property (
    @(posedge clk) disable iff (!clk) (up_down == 0 && q == 7) |-> q == 0
  );
  // Counter wraps around to 7 when up_down is 1 and q is 0.
  counter_wrap_down: assert property (
    @(posedge clk) disable iff (!clk) (up_down == 1 && q == 0) |-> q == 7
  );

endmodule
```
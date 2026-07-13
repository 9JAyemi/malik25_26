module counter_mod_sva (
  input logic clk,
  input logic rst,
  input logic up_down,
  output logic [3:0] q,
  output logic carry
);

  ///// Counter behavior /////
  // Up counter: q should increment by 1 on each positive edge of clk when up_down is 0.
  up_counter: assert property (
    @(posedge clk) disable iff (!rst) (up_down == 1'b0) |-> (q == q + 4'b1)
  );

  // Down counter: q should decrement by 1 on each positive edge of clk when up_down is 1.
  down_counter: assert property (
    @(posedge clk) disable iff (!rst) (up_down == 1'b1) |-> (q == q - 4'b1)
  );

  // Counter should wrap around to 0 when it reaches 15 (4'b1111) and carry should be set.
  counter_wrap_up: assert property (
    @(posedge clk) disable iff (!rst) (q == 4'b1111) |-> (q == 4'b0000) && (carry == 1'b1)
  );

  // Counter should wrap around to 15 (4'b1111) when it reaches 0 (4'b0000) and carry should be set.
  counter_wrap_down: assert property (
    @(posedge clk) disable iff (!rst) (q == 4'b0000) |-> (q == 4'b1111) && (carry == 1'b1)
  );

  // Counter should not change when reset is active.
  counter_reset: assert property (
    @(posedge clk) !rst |-> q == q
  );

  // Carry should be set when counter wraps around.
  carry_set: assert property (
    @(posedge clk) disable iff (!rst) (q == 4'b1111) |-> carry == 1'b1
  );

  // Carry should be cleared when counter does not wrap around.
  carry_clear: assert property (
    @(posedge clk) disable iff (!rst) (q != 4'b1111) |-> carry == 1'b0
  );

  // Up counter should not wrap around when it reaches 15.
  up_counter_no_wrap: assert property (
    @(posedge clk) disable iff (!rst) (q == 4'b1111) |-> up_down == 1'b1
  );

  // Down counter should not wrap around when it reaches 0.
  down_counter_no_wrap: assert property (
    @(posedge clk) disable iff (!rst) (q == 4'b0000) |-> up_down == 1'b0
  );

endmodule
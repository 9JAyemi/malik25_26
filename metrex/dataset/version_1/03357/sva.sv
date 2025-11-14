// SVA for binary_counter
module binary_counter_sva (
  input logic clk,
  input logic rst,
  input logic Q1,
  input logic Q0
);

  // Asynchronous reset must clear outputs immediately (same time step)
  assert property (@(negedge rst) 1 |-> ##0 (Q1==1'b0 && Q0==1'b0));

  // While in reset, outputs are held low at clock edges
  assert property (@(posedge clk) !rst |-> (Q1==1'b0 && Q0==1'b0));

  // First cycle after reset release -> 01
  assert property (@(posedge clk) $rose(rst) |=> (Q1==1'b0 && Q0==1'b1));

  // When rst is high in consecutive cycles: Q0 toggles; Q1 tracks previous Q0
  assert property (@(posedge clk) rst && $past(rst)
                   |-> (Q0 == ~ $past(Q0) && Q1 == $past(Q0)));

  // Valid encoding when out of reset: exactly one bit high (01 or 10), no X/Z
  assert property (@(posedge clk) rst |-> (Q1 !== Q0) && ! $isunknown({Q1,Q0}));

  // Coverage: see both legal states and both transitions after reset release
  cover property (@(posedge clk) $rose(rst)
                  ##1 (Q1==0 && Q0==1) ##1 (Q1==1 && Q0==0)
                  ##1 (Q1==0 && Q0==1));

  cover property (@(posedge clk) rst && $past(rst)
                  ##1 (Q1==1 && Q0==0) ##1 (Q1==0 && Q0==1));

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk(clk), .rst(rst), .Q1(Q1), .Q0(Q0)
);
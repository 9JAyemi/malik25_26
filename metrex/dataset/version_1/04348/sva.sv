// SVA for async_ff
// Active-low reset (rst==0 -> in reset)
`ifndef ASYNC_FF_SVA
`define ASYNC_FF_SVA

module async_ff_sva (
  input logic clk,
  input logic rst,
  input logic en,
  input logic d,
  input logic q,
  input logic q_d
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst);

  // q is a 1-cycle delayed copy of q_d (out of reset)
  assert property (q == $past(q_d))
    else $error("q must equal $past(q_d)");

  // Capture and hold behavior of q_d
  assert property (en  |=> (q_d == $past(d)))
    else $error("q_d must capture d when en=1");
  assert property (!en |=> (q_d == $past(q_d)))
    else $error("q_d must hold when en=0");

  // End-to-end propagation: d -> q in 2 cycles when enabled
  assert property (en |-> ##2 (q == $past(d,2)))
    else $error("q must reflect d two cycles after en");

  // No X/Z on state when out of reset
  assert property (!$isunknown(q_d))
    else $error("q_d X/Z out of reset");
  assert property (!$isunknown(q))
    else $error("q X/Z out of reset");

  // Asynchronous reset effect observed at clock edge
  assert property (@(posedge clk) !rst |-> (q_d==1'b0 && q==1'b0))
    else $error("During rst=0 at clk, q_d and q must be 0");

  // Coverage
  cover property (rst ##1 en ##2 (q == $past(d,2)));       // capture and observe at q
  cover property (rst ##1 !en ##1 (q_d == $past(q_d)));    // hold behavior

endmodule

// Bind into DUT (connects to internal q_d)
bind async_ff async_ff_sva u_async_ff_sva (
  .clk(clk), .rst(rst), .en(en), .d(d), .q(q), .q_d(q_d)
);

`endif
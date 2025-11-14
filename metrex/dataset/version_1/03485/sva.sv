// SVA for serdes_fc_tx
// Bind example:
// bind serdes_fc_tx serdes_fc_tx_sva sva(.clk(clk), .rst(rst), .xon_rcvd(xon_rcvd), .xoff_rcvd(xoff_rcvd), .inhibit_tx(inhibit_tx), .state(state));

module serdes_fc_tx_sva
(
  input clk, input rst,
  input xon_rcvd, input xoff_rcvd,
  input inhibit_tx,
  input [15:0] state
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // safe $past usage
  logic past_valid;
  always @(posedge clk) past_valid <= !rst;

  // Exact next-state function (priority: rst > xoff > xon > dec > hold)
  assert property (past_valid |-> state ==
                     ( $past(rst)            ? 16'd0 :
                       $past(xoff_rcvd)      ? 16'd255 :
                       $past(xon_rcvd)       ? 16'd0 :
                       ($past(state)!=16'd0) ? ($past(state)-16'd1) :
                                               $past(state)));

  // inhibit_tx reflects previous cycle's (state != 0)
  assert property (past_valid |-> inhibit_tx == ($past(state)!=16'd0));

  // State never exceeds 255
  assert property (state <= 16'd255);

  // Explicit precedence: xoff over xon when both asserted
  assert property (past_valid && $past(xon_rcvd && xoff_rcvd) |-> state==16'd255);

  // Coverage

  // Count-down from XOFF to zero at some point (may be early via XON)
  cover property (xoff_rcvd ##1 state==16'd255 ##[1:260] state==16'd0);

  // XON while nonzero forces state to zero next cycle
  cover property (state!=16'd0 ##1 xon_rcvd ##1 state==16'd0);

  // Simultaneous XON & XOFF picks XOFF path
  cover property (xon_rcvd && xoff_rcvd ##1 state==16'd255);

  // Idle zeros observed
  cover property (state==16'd0 [*8]);

  // Inhibit rises two cycles after XOFF when previously idle at zero
  cover property (state==16'd0 [*2] ##1 xoff_rcvd ##2 inhibit_tx);

endmodule
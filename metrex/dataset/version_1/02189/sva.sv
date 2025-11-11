// SVA for baudgen: concise, high-quality checks and coverage.
// Bind this checker to the DUT.

module baudgen_sva
  #(parameter int RWIDTH = 25)
  (
    input  logic                  clk,
    input  logic                  resetq,
    input  logic [31:0]           baud,
    input  logic                  restart,
    input  logic                  ser_clk,
    // internal DUT signals (visible in bind scope)
    input  logic [RWIDTH-1:0]     d,
    input  logic [RWIDTH-1:0]     aclkfreq
  );

  default clocking cb @(posedge clk); endclocking

  // Local view of truncated baud used by DUT arithmetic
  logic [RWIDTH-1:0] baud25;
  assign baud25 = {4'd0, baud}[RWIDTH-1:0];

  // Combinational relation of ser_clk to accumulator MSB
  assert property (cb disable iff (!resetq)
    ser_clk == ~d[RWIDTH-1]
  );

  // Asynchronous reset: immediate effect on d and ser_clk
  assert property (@(negedge resetq)
    ##0 (d == '0 && ser_clk == 1'b1)
  );

  // While held in reset, state is held at zero and ser_clk high
  assert property (cb !resetq |-> (d == '0 && ser_clk == 1'b1));

  // aclkfreq is a constant inside DUT (should never change)
  assert property (cb $stable(aclkfreq));

  // Correct sequential update of accumulator (wrap-aware by sizing)
  // Matches DUT expression: d <= restart ? 0 : d + (d[MSB] ? baud25 : baud25 - aclkfreq)
  assert property (cb disable iff (!resetq)
    d == $past( restart ? '0
                        : ( d + ( d[RWIDTH-1] ? baud25 : (baud25 - aclkfreq) ) ) )
  );

  // Restart causes accumulator to clear on the very next clk edge
  assert property (cb disable iff (!resetq)
    $past(restart) |-> (d == '0)
  );

  // ser_clk only changes when d changes (no spurious toggles at clk boundaries)
  assert property (cb disable iff (!resetq)
    ($changed(ser_clk)) |-> ($changed(d))
  );

  // -------- Coverage --------

  // Observe both edges of ser_clk
  cover property (cb disable iff (!resetq) $rose(ser_clk));
  cover property (cb disable iff (!resetq) $fell(ser_clk));

  // Both accumulator MSB regions exercised (both dInc branches)
  cover property (cb disable iff (!resetq) (d[RWIDTH-1] == 1'b0) ##1 (d[RWIDTH-1] == 1'b1));
  cover property (cb disable iff (!resetq) (d[RWIDTH-1] == 1'b1) ##1 (d[RWIDTH-1] == 1'b0));

  // Restart pulse observed and clears accumulator
  cover property (cb disable iff (!resetq) restart ##1 (d == '0));

  // Asynchronous reset observed
  cover property (@(negedge resetq) 1'b1);

endmodule

// Bind into the DUT
bind baudgen baudgen_sva #(.RWIDTH(RWIDTH)) u_baudgen_sva (
  .clk(clk),
  .resetq(resetq),
  .baud(baud),
  .restart(restart),
  .ser_clk(ser_clk),
  .d(d),
  .aclkfreq(aclkfreq)
);
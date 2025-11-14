// SVA for ballscan. Bind this to the DUT.
// Focus: precise cycle-accurate semantics (including blocking-assign ordering), bounds, and key coverpoints.

module ballscan_sva #(
  parameter int BALLSIZE = 8
)(
  input  logic        clk,
  input  logic [9:0]  screenx,
  input  logic [9:0]  screeny,
  input  logic [9:0]  ball_x,
  input  logic [9:0]  ball_y,
  input  logic [3:0]  ballscanX,
  input  logic        ballscanY,
  input  logic        ball_scan
);

  localparam int HALF = BALLSIZE/2;

  // Handy events/terms
  wire x_reload   = (screenx == (ball_x - HALF));
  wire y_top_hit  = (screeny == (ball_y - HALF));
  wire y_bot_hit  = (screeny == (ball_y + HALF));

  // Past-valid guard for $past/$rose/$fell usage
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // ballscanX exact next-state semantics (blocking assigns cause 12 -> 11 on reload cycle)
  assert property (x_reload |=> ballscanX == 4'd11);
  assert property (!x_reload && past_valid && $past(ballscanX) > 0 |=> ballscanX == $past(ballscanX) - 1);
  assert property (!x_reload && past_valid && $past(ballscanX) == 0 |=> ballscanX == 0);

  // ballscanX bounds and monotonicity
  assert property (!($isunknown(ballscanX)) |-> ballscanX <= 4'd11);

  // ballscanY exact next-state semantics (bottom overrides top if both would hit)
  assert property (y_bot_hit |=> ballscanY == 1'b0);
  assert property (y_top_hit && !y_bot_hit |=> ballscanY == 1'b1);
  assert property (!y_top_hit && !y_bot_hit && past_valid |=> ballscanY == $past(ballscanY));

  // ballscanY edges can only occur on corresponding y hits
  assert property (past_valid && $rose(ballscanY) |-> y_top_hit && !y_bot_hit);
  assert property (past_valid && $fell(ballscanY) |-> y_bot_hit);

  // Output gating (combinational consistency)
  assert property (ballscanX == 0 |-> !ball_scan);
  assert property (!ballscanY    |-> !ball_scan);
  assert property (ball_scan |-> (ballscanX != 0 && ballscanY));

  // Coverage
  cover property (x_reload);
  cover property (y_top_hit ##[1:$] y_bot_hit);
  cover property (ball_scan);

  // Full horizontal countdown after a reload (no further reloads during the run)
  cover property (
    x_reload ##1
    (ballscanX==4'd11) ##1 (ballscanX==4'd10) ##1 (ballscanX==4'd9)  ##1
    (ballscanX==4'd8)  ##1 (ballscanX==4'd7)  ##1 (ballscanX==4'd6)  ##1
    (ballscanX==4'd5)  ##1 (ballscanX==4'd4)  ##1 (ballscanX==4'd3)  ##1
    (ballscanX==4'd2)  ##1 (ballscanX==4'd1)  ##1 (ballscanX==4'd0)
  );

endmodule

// Bind to the DUT (access internal regs)
bind ballscan ballscan_sva #(.BALLSIZE(BALLSIZE)) u_ballscan_sva (
  .clk       (clk),
  .screenx   (screenx),
  .screeny   (screeny),
  .ball_x    (ball_x),
  .ball_y    (ball_y),
  .ballscanX (ballscanX),
  .ballscanY (ballscanY),
  .ball_scan (ball_scan)
);
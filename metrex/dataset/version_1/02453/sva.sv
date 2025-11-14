// SVA bind file for ballcollisions
module ballcollisions_sva #(
  int HC      = 0,
  int VA      = 0,
  int VC      = 0,
  int BATW    = 0,
  int BATHT   = 0,
  int BALLSZ  = 0
)(
  input  logic clk,
  input  logic reset,

  // DUT ports
  input  int   p1_y,
  input  int   p2_y,
  input  logic dir_x,
  input  logic dir_y,
  input  logic oob,

  // DUT internals (bound hierarchically)
  input  int   ball_x_reg,
  input  int   ball_y_reg,
  input  logic dir_x_reg,
  input  logic dir_y_reg,
  input  logic oob_reg
);
  default clocking cb @(posedge clk); endclocking

  // past_valid helper
  logic past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Derived hit conditions (evaluate on $past state because of non-blocking updates)
  function automatic bit p1_hit_f;
    p1_hit_f = ($past(ball_x_reg) <= BATW) &&
               ($past(ball_y_reg) + BALLSZ >= $past(p1_y)) &&
               ($past(ball_y_reg) <= $past(p1_y) + BATHT);
  endfunction

  function automatic bit p2_hit_f;
    p2_hit_f = ($past(ball_x_reg) >= (HC - BATW - BALLSZ)) &&
               ($past(ball_y_reg) + BALLSZ <= $past(p2_y) + BATHT) &&
               ($past(ball_y_reg) >= $past(p2_y));
  endfunction

  function automatic bit top_hit_f;
    top_hit_f = ($past(ball_y_reg) <= (VA + BALLSZ));
  endfunction

  function automatic bit bot_hit_f;
    bot_hit_f = ($past(ball_y_reg) >= (VC - BALLSZ));
  endfunction

  // Outputs mirror internal regs
  assert property (dir_x == dir_x_reg && dir_y == dir_y_reg && oob == oob_reg);

  // Reset behavior (nonblocking assigns take effect on the reset edge)
  assert property (reset |-> (dir_y_reg == 1'b1 && oob_reg == 1'b0 &&
                              ball_x_reg == HC && ball_y_reg == (VC/2)));
  assert property (reset && past_valid |-> dir_x_reg == ~$past(dir_x_reg));

  // Out-of-bounds flag corresponds to previous X location
  assert property (!reset && past_valid |-> oob_reg == (($past(ball_x_reg) <= 0) || ($past(ball_x_reg) >= HC)));

  // Ball movement uses previous dir regs
  assert property (!reset && past_valid &&  $past(dir_x_reg) |-> ball_x_reg == $past(ball_x_reg) + 1);
  assert property (!reset && past_valid && !$past(dir_x_reg) |-> ball_x_reg == $past(ball_x_reg) - 1);
  assert property (!reset && past_valid &&  $past(dir_y_reg) |-> ball_y_reg == $past(ball_y_reg) + 1);
  assert property (!reset && past_valid && !$past(dir_y_reg) |-> ball_y_reg == $past(ball_y_reg) - 1);

  // Wall collisions set Y direction
  assert property (!reset && past_valid && top_hit_f() |-> dir_y_reg == 1'b1);
  assert property (!reset && past_valid && bot_hit_f() |-> dir_y_reg == 1'b0);

  // Paddle collisions set X and Y direction; P1 has precedence over P2 (else-if)
  assert property (!reset && past_valid && p1_hit_f() |-> (dir_x_reg == 1'b1) &&
                   (dir_y_reg == ((($past(ball_y_reg) + BALLSZ) <= ($past(p1_y) + (BATHT/2))) ? 1'b0 : 1'b1)));
  assert property (!reset && past_valid && !p1_hit_f() && p2_hit_f() |-> (dir_x_reg == 1'b0) &&
                   (dir_y_reg == ((($past(ball_y_reg) + BALLSZ) <= ($past(p2_y) + (BATHT/2))) ? 1'b0 : 1'b1)));
  assert property (!reset && past_valid && p1_hit_f() && p2_hit_f() |-> dir_x_reg == 1'b1);

  // Dir holds when no events
  assert property (!reset && past_valid && !p1_hit_f() && !p2_hit_f() |-> dir_x_reg == $past(dir_x_reg));
  assert property (!reset && past_valid && !top_hit_f() && !bot_hit_f() && !p1_hit_f() && !p2_hit_f()
                   |-> dir_y_reg == $past(dir_y_reg));

  // Coverage: reset, walls, paddles (both halves), OOB left/right
  cover property (past_valid ##1 reset);
  cover property (past_valid && top_hit_f());
  cover property (past_valid && bot_hit_f());
  cover property (past_valid && p1_hit_f());
  cover property (past_valid && !p1_hit_f() && p2_hit_f());

  cover property (past_valid && p1_hit_f() &&
                  (($past(ball_y_reg) + BALLSZ) <= ($past(p1_y) + (BATHT/2))));
  cover property (past_valid && p1_hit_f() &&
                  (($past(ball_y_reg) + BALLSZ) >  ($past(p1_y) + (BATHT/2))));
  cover property (past_valid && !p1_hit_f() && p2_hit_f() &&
                  (($past(ball_y_reg) + BALLSZ) <= ($past(p2_y) + (BATHT/2))));
  cover property (past_valid && !p1_hit_f() && p2_hit_f() &&
                  (($past(ball_y_reg) + BALLSZ) >  ($past(p2_y) + (BATHT/2))));

  cover property (past_valid && ($past(ball_x_reg) <= 0));
  cover property (past_valid && ($past(ball_x_reg) >= HC));
endmodule

// Bind into DUT; pass DUT constants into SVA
bind ballcollisions ballcollisions_sva #(
  .HC(hc), .VA(va), .VC(vc), .BATW(batwidth), .BATHT(batheight), .BALLSZ(ballsize)
) ballcollisions_sva_i (
  .clk(clk),
  .reset(reset),
  .p1_y(p1_y),
  .p2_y(p2_y),
  .dir_x(dir_x),
  .dir_y(dir_y),
  .oob(oob),
  .ball_x_reg(ball_x_reg),
  .ball_y_reg(ball_y_reg),
  .dir_x_reg(dir_x_reg),
  .dir_y_reg(dir_y_reg),
  .oob_reg(oob_reg)
);
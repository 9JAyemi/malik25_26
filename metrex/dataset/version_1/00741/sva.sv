// SVA checker for game_graph
// Bind this file to the DUT.
// Focused, high-signal-quality assertions with targeted coverage.

module game_graph_sva
(
  input  logic        clk, reset,
  input  logic        video_on, gra_still,
  input  logic [2:0]  sw,
  input  logic [9:0]  pix_x, pix_y,
  input  logic        refr_tick,

  // State regs
  input  logic [9:0]  bar_y_reg, gun_y_reg,
  input  logic [9:0]  bullet_x_reg, bullet_y_reg,
  input  logic [9:0]  ball_x_reg, ball_y_reg,
  input  logic [9:0]  x_delta_reg, y_delta_reg,

  // On/Color/RGB
  input  logic        wall_on, bar_on, gun_on, bullet_on, rd_ball_on,
  input  logic [2:0]  wall_rgb, bar_rgb, gun_rgb, bullet_rgb, ball_rgb, graph_rgb,
  input  logic        graph_on,

  // Events
  input  logic        hit, miss, kill
);

  // Constants (must match DUT)
  localparam int MAX_X=640, MAX_Y=480;
  localparam int WALL_X_L=20,  WALL_X_R=25;
  localparam int GUN_X_L=50,   GUN_X_R=53,  GUN_V=2,  GUN_Y_SIZE=62;
  localparam int BULLET_SIZE=9, BULLET_V=5;
  localparam int BAR_X_L=600,  BAR_X_R=603, BAR_Y_SIZE=72, BAR_V=4;
  localparam int BALL_SIZE=8;
  localparam int signed BALL_V_P=+2, BALL_V_N=-2;

  // Derived geometry
  logic [9:0] bar_y_t, bar_y_b, gun_y_t, gun_y_b;
  logic [9:0] bullet_x_l, bullet_x_r, bullet_y_t, bullet_y_b;
  logic [9:0] ball_x_l, ball_x_r, ball_y_ti, ball_y_b;

  assign bar_y_t = bar_y_reg;
  assign bar_y_b = bar_y_reg + BAR_Y_SIZE - 1;
  assign gun_y_t = gun_y_reg;
  assign gun_y_b = gun_y_reg + GUN_Y_SIZE - 1;

  assign bullet_x_l = bullet_x_reg;
  assign bullet_x_r = bullet_x_reg + BULLET_SIZE - 1;
  assign bullet_y_t = bullet_y_reg;
  assign bullet_y_b = bullet_y_reg + BULLET_SIZE - 1;

  assign ball_x_l = ball_x_reg;
  assign ball_x_r = ball_x_reg + BALL_SIZE - 1;
  assign ball_y_ti = ball_y_reg;
  assign ball_y_b = ball_y_reg + BALL_SIZE - 1;

  // Centers
  localparam int CENTER_BAR_Y = (MAX_Y - BAR_Y_SIZE)/2;
  localparam int CENTER_GUN_Y = (MAX_Y - GUN_Y_SIZE)/2;
  localparam int CENTER_BALL_X = MAX_X/2;
  localparam int CENTER_BALL_Y = MAX_Y/2;

  // Default clock
  default clocking cb @(posedge clk); endclocking

  // 1) Refr tick equivalence
  assert property (disable iff (reset)
    refr_tick == ((pix_y==10'd481) && (pix_x==10'd0))
  );

  // 2) Movement gating when no refr_tick and not gra_still
  assert property (disable iff (reset) (!gra_still && !refr_tick) |=> $stable(bar_y_reg));
  assert property (disable iff (reset) (!gra_still && !refr_tick) |=> $stable(gun_y_reg));
  assert property (disable iff (reset) (!gra_still && !refr_tick) |=> $stable(bullet_x_reg) && $stable(bullet_y_reg));
  assert property (disable iff (reset) (!gra_still && !refr_tick) |=> $stable(ball_x_reg) && $stable(ball_y_reg));

  // 3) gra_still forces centers and ball deltas
  assert property (disable iff (reset)
    gra_still |=> (bar_y_reg==CENTER_BAR_Y &&
                   gun_y_reg==CENTER_GUN_Y &&
                   bullet_x_reg==GUN_X_R &&
                   bullet_y_reg==CENTER_GUN_Y + GUN_Y_SIZE/2 &&
                   ball_x_reg==CENTER_BALL_X &&
                   ball_y_reg==CENTER_BALL_Y &&
                   $signed(x_delta_reg)==BALL_V_N &&
                   $signed(y_delta_reg)==BALL_V_P)
  );

  // 4) Ball moves by its deltas on refr_tick
  assert property (disable iff (reset)
    (!gra_still && refr_tick) |=> (ball_x_reg == $past(ball_x_reg) + $signed($past(x_delta_reg)) &&
                                   ball_y_reg == $past(ball_y_reg) + $signed($past(y_delta_reg)))
  );

  // 5) Bar/Gun step sizes per update
  assert property (disable iff (reset)
    (!gra_still && refr_tick && (bar_y_reg != $past(bar_y_reg))) |->
      (bar_y_reg == $past(bar_y_reg)+BAR_V || bar_y_reg == $past(bar_y_reg)-BAR_V)
  );
  assert property (disable iff (reset)
    (!gra_still && refr_tick && (gun_y_reg != $past(gun_y_reg))) |->
      (gun_y_reg == $past(gun_y_reg)+GUN_V || gun_y_reg == $past(gun_y_reg)-GUN_V)
  );

  // 6) Range constraints
  assert property (bar_y_reg <= (MAX_Y - BAR_Y_SIZE));
  assert property (gun_y_reg <= (MAX_Y - GUN_Y_SIZE));
  assert property (bullet_y_reg <= (MAX_Y - BULLET_SIZE));

  // 7) Bullet motion semantics
  // Move when refr_tick and (sw[1] || left >= GUN_X_R+5)
  assert property (disable iff (reset)
    (!gra_still && refr_tick && (sw[1] || (bullet_x_reg >= GUN_X_R+5))) |=> 
      (bullet_x_reg == $past(bullet_x_reg) + BULLET_V && bullet_y_reg == $past(bullet_y_reg))
  );
  // Otherwise reset to gun center (when not killing)
  assert property (disable iff (reset)
    (!gra_still && refr_tick && !(sw[1] || (bullet_x_reg >= GUN_X_R+5)) && !kill) |=> 
      (bullet_x_reg == GUN_X_R && bullet_y_reg == $past(gun_y_reg) + GUN_Y_SIZE/2)
  );
  // Kill implies bar overlap and reset next cycle
  wire bullet_bar_ov = (bullet_x_r >= BAR_X_L && bullet_x_r <= BAR_X_R) &&
                       (bar_y_t <= bullet_y_b) && (bullet_y_t <= bar_y_b);
  assert property (disable iff (reset) kill |->
    (refr_tick && !gra_still && bullet_bar_ov)
  );
  assert property (disable iff (reset) kill |=> 
    (bullet_x_reg == GUN_X_R && bullet_y_reg == $past(gun_y_reg) + GUN_Y_SIZE/2)
  );

  // 8) Ball collision responses
  wire ball_bar_ov = (ball_x_r >= BAR_X_L && ball_x_r <= BAR_X_R) &&
                     (bar_y_t <= ball_y_b) && (ball_y_ti <= bar_y_b);
  assert property (disable iff (reset)
    hit |->
      (!gra_still && ball_bar_ov &&
       !(ball_y_ti < 1) &&
       !(ball_y_b > (MAX_Y-1)) &&
       !(ball_x_l <= WALL_X_R))
  );
  assert property (disable iff (reset) hit |=> $signed(x_delta_reg) == BALL_V_N);
  assert property (disable iff (reset) (!gra_still && (ball_y_ti < 1)) |=> $signed(y_delta_reg) == BALL_V_P);
  assert property (disable iff (reset) (!gra_still && (ball_y_b > (MAX_Y-1))) |=> $signed(y_delta_reg) == BALL_V_N);
  assert property (disable iff (reset) (!gra_still && (ball_x_l <= WALL_X_R)) |=> $signed(x_delta_reg) == BALL_V_P);
  assert property (disable iff (reset) miss |->
    (!gra_still && (ball_x_r > MAX_X))
  );

  // 9) Delta value domain
  assert property ($signed(x_delta_reg) == BALL_V_P || $signed(x_delta_reg) == BALL_V_N || (x_delta_reg == 10'd4));
  assert property ($signed(y_delta_reg) == BALL_V_P || $signed(y_delta_reg) == BALL_V_N || (y_delta_reg == 10'd4));

  // 10) On-region correctness for key shapes
  assert property (wall_on == ((pix_x>=WALL_X_L) && (pix_x<=WALL_X_R)));
  assert property (bar_on  == ((pix_x>=BAR_X_L)  && (pix_x<=BAR_X_R)  &&
                               (pix_y>=bar_y_t)  && (pix_y<=bar_y_b)));
  assert property (gun_on  == ((pix_x>=GUN_X_L)  && (pix_x<=GUN_X_R)  &&
                               (pix_y>=gun_y_t)  && (pix_y<=gun_y_b)));
  assert property (bullet_on == ((pix_x>=bullet_x_l) && (pix_x<=bullet_x_r) &&
                                 (pix_y>=bullet_y_t) && (pix_y<=bullet_y_b)));

  // 11) graph_on and RGB priority
  assert property (graph_on == (wall_on | bar_on | rd_ball_on | bullet_on | gun_on));
  assert property ((!video_on) |-> (graph_rgb == 3'b000));
  assert property ((video_on && wall_on) |-> (graph_rgb == wall_rgb));
  assert property ((video_on && !wall_on && bullet_on) |-> (graph_rgb == bullet_rgb));
  assert property ((video_on && !wall_on && !bullet_on && bar_on) |-> (graph_rgb == bar_rgb));
  assert property ((video_on && !wall_on && !bullet_on && !bar_on && gun_on) |-> (graph_rgb == gun_rgb));
  assert property ((video_on && !wall_on && !bullet_on && !bar_on && !gun_on && rd_ball_on) |-> (graph_rgb == ball_rgb));
  assert property ((video_on && !(wall_on|bullet_on|bar_on|gun_on|rd_ball_on)) |-> (graph_rgb == 3'b110));

  // 12) Coverage
  cover property (hit);
  cover property (miss);
  cover property (kill);
  cover property (!gra_still && refr_tick && sw[1] ##1 (bullet_x_reg == $past(bullet_x_reg)+BULLET_V));
  cover property (!gra_still && (ball_x_l <= WALL_X_R) ##1 ($signed(x_delta_reg) == BALL_V_P));
  cover property (!gra_still && (ball_y_ti < 1) ##1 ($signed(y_delta_reg) == BALL_V_P));
  cover property (!gra_still && (ball_y_b > (MAX_Y-1)) ##1 ($signed(y_delta_reg) == BALL_V_N));
  cover property (video_on && wall_on);
  cover property (video_on && !wall_on && bullet_on);
  cover property (video_on && !wall_on && !bullet_on && bar_on);
  cover property (video_on && !wall_on && !bullet_on && !bar_on && gun_on);
  cover property (video_on && !(wall_on|bullet_on|bar_on|gun_on) && rd_ball_on);
  cover property (video_on && !(wall_on|bullet_on|bar_on|gun_on|rd_ball_on));
endmodule

// Bind to DUT
bind game_graph game_graph_sva SVA_I
(
  .clk(clk), .reset(reset),
  .video_on(video_on), .gra_still(gra_still), .sw(sw),
  .pix_x(pix_x), .pix_y(pix_y),
  .refr_tick(refr_tick),

  .bar_y_reg(bar_y_reg), .gun_y_reg(gun_y_reg),
  .bullet_x_reg(bullet_x_reg), .bullet_y_reg(bullet_y_reg),
  .ball_x_reg(ball_x_reg), .ball_y_reg(ball_y_reg),
  .x_delta_reg(x_delta_reg), .y_delta_reg(y_delta_reg),

  .wall_on(wall_on), .bar_on(bar_on), .gun_on(gun_on), .bullet_on(bullet_on), .rd_ball_on(rd_ball_on),
  .wall_rgb(wall_rgb), .bar_rgb(bar_rgb), .gun_rgb(gun_rgb), .bullet_rgb(bullet_rgb), .ball_rgb(ball_rgb), .graph_rgb(graph_rgb),
  .graph_on(graph_on),

  .hit(hit), .miss(miss), .kill(kill)
);
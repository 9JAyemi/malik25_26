// SVA for tri_light_svetofor
// Bind module (concise, checks timer, color decode, blink, reset, and coverage)

module tri_light_svetofor_sva #(
  parameter int unsigned GREEN_TIME = 52,
  parameter int unsigned RED_TIME   = 168,
  parameter int unsigned YELLOW_TIME= 6,
  parameter int unsigned BLNK_TIME  = 8,
  parameter int unsigned TRIL_TIME  = GREEN_TIME + BLNK_TIME + RED_TIME + 2*YELLOW_TIME
)(
  input  logic        clk,
  input  logic        rst_n,         // active-low reset
  input  logic [7:0]  timer,
  input  logic [2:0]  sel_color,
  input  logic        red, yellow, green
);

  // timing landmarks
  localparam int unsigned T0 = RED_TIME;
  localparam int unsigned T1 = RED_TIME + YELLOW_TIME;
  localparam int unsigned T2 = T1 + GREEN_TIME;
  localparam int unsigned T3 = T2 + BLNK_TIME;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // past-valid to guard $past use
  logic past_valid;
  always @(posedge clk or negedge rst_n)
    if (!rst_n) past_valid <= 1'b0; else past_valid <= 1'b1;

  // Asynchronous reset behavior
  assert property (@(negedge rst_n) timer==8'd0 && sel_color==3'b110);

  // Outputs match sel_color bits
  assert property (red    == sel_color[0]);
  assert property (yellow == sel_color[1]);
  assert property (green  == sel_color[2]);

  // No X/Z on key signals
  assert property (!$isunknown({timer, sel_color, red, yellow, green}));

  // Timer range and next-state behavior
  assert property (timer <= TRIL_TIME);
  assert property (past_valid && (timer <  TRIL_TIME) |=> timer == $past(timer)+1);
  assert property (past_valid && (timer >= TRIL_TIME) |=> timer == 8'd0);

  // Color decode by timer range (next-state checks)
  assert property (past_valid && (timer <= T0)                         |=> sel_color == 3'b110);
  assert property (past_valid && (timer >  T0 && timer <= T1)          |=> sel_color == 3'b100);
  assert property (past_valid && (timer >  T1 && timer <= T2)          |=> sel_color == 3'b011);
  // Blink window: toggle between 011 and 111 based on previous sel_color
  assert property (past_valid && (timer >  T2 && timer <= T3)          |=> ($past(sel_color)==3'b011) ? sel_color==3'b111 : sel_color==3'b011);
  assert property (past_valid && (timer >  T3)                         |=> sel_color == 3'b101);

  // Boundary correctness (single-cycle next-state checks)
  assert property (past_valid && (timer==T0) |=> sel_color==3'b110);
  assert property (past_valid && (timer==T1) |=> sel_color==3'b100);
  assert property (past_valid && (timer==T2) |=> sel_color==3'b011);
  assert property (past_valid && (timer==T3) |=> (($past(sel_color)==3'b011) ? sel_color==3'b111 : sel_color==3'b011));

  // Coverage
  // Wrap coverage
  cover property (past_valid && (timer==TRIL_TIME) |=> timer==8'd0);

  // Blink toggling coverage (011 -> 111 -> 011 within blink window)
  cover property (
    past_valid && (timer > T2 && timer <= T3) ##1
    (timer > T2 && timer <= T3) && $past(sel_color)==3'b011 && sel_color==3'b111 ##1
    (timer > T2 && timer <= T3) && sel_color==3'b011
  );

  // See all encodings in a cycle
  cover property (sel_color==3'b110 ##[1:$] sel_color==3'b100 ##[1:$] sel_color==3'b011 ##[1:$] sel_color==3'b111 ##[1:$] sel_color==3'b101);

endmodule

// Bind into DUT (parameters taken from DUT)
bind tri_light_svetofor tri_light_svetofor_sva #(
  .GREEN_TIME (green_time),
  .RED_TIME   (red_time),
  .YELLOW_TIME(yellow_time),
  .BLNK_TIME  (blnk_time),
  .TRIL_TIME  (tril_time)
) i_tri_light_svetofor_sva (
  .clk       (time_signal),
  .rst_n     (reset),
  .timer     (timer),
  .sel_color (sel_color),
  .red       (red),
  .yellow    (yellow),
  .green     (green)
);
// SVA for ps2_rx
// Bindable, concise checks of state machine, counters, shifter, filter, and outputs.
`ifndef PS2_RX_SVA
`define PS2_RX_SVA

module ps2_rx_sva
(
  input  logic        clk, reset,
  input  logic        ps2d, ps2c,
  input  logic        rx_en,
  input  logic        rx_done_tick,
  input  logic [7:0]  dout,

  // DUT internals
  input  logic [1:0]  state_reg,
  input  logic [7:0]  filter_reg,
  input  logic        f_ps2c_reg,
  input  logic [3:0]  n_reg,
  input  logic [10:0] b_reg,
  input  logic        fall_edge
);

  localparam logic [1:0] idle = 2'b00, dps = 2'b01, load = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // State encoding must be legal
  assert property (state_reg inside {idle, dps, load});

  // When reset is asserted, registers are forced low/idle
  assert property (reset |-> filter_reg==8'h00 && f_ps2c_reg==1'b0 &&
                            state_reg==idle && n_reg==4'd0 && b_reg==11'd0);

  // Filter pipeline and filtered clock state update
  assert property ($past(!reset) |-> filter_reg == { $past(ps2c), $past(filter_reg[7:1])});
  assert property ($past(!reset) |-> f_ps2c_reg ==
                   ( ($past(filter_reg)==8'hFF) ? 1'b1 :
                     ($past(filter_reg)==8'h00) ? 1'b0 : $past(f_ps2c_reg)));

  // fall_edge implies filtered ps2c falls on next cycle
  assert property ($past(!reset) && $past(fall_edge) |-> $past(f_ps2c_reg) && !f_ps2c_reg);

  // State transitions
  assert property ($past(state_reg)==idle |-> state_reg ==
                   ( $past(fall_edge && rx_en) ? dps : idle));

  assert property ($past(state_reg)==dps  |-> state_reg ==
                   ( $past(fall_edge) ? ($past(n_reg)==0 ? load : dps) : dps));

  assert property ($past(state_reg)==load |-> state_reg == idle);

  // Gating in idle: ignore clock edges when rx_en==0
  assert property ($past(state_reg)==idle && $past(fall_edge) && !$past(rx_en)
                   |-> state_reg==idle && n_reg==$past(n_reg) && b_reg==$past(b_reg));

  // Bit counter behavior
  assert property ($past(state_reg)==idle && $past(fall_edge && rx_en) |-> n_reg==4'd9);
  assert property ($past(state_reg)==dps && $past(fall_edge) && $past(n_reg)>0
                   |-> n_reg==$past(n_reg)-1);
  assert property ($past(state_reg)==dps && $past(fall_edge) && $past(n_reg)==0
                   |-> n_reg==0);

  // Shift register behavior
  assert property ($past(!reset) && $past(fall_edge) &&
                   ($past(state_reg)==dps || ($past(state_reg)==idle && $past(rx_en)))
                   |-> b_reg == { $past(ps2d), $past(b_reg[10:1])});

  assert property ($past(!reset) && !$past(fall_edge) |-> b_reg==$past(b_reg));

  // Output mapping and rx_done_tick pulse
  assert property (dout == b_reg[8:1]);
  assert property (rx_done_tick == (state_reg==load));
  assert property (rx_done_tick |-> ##1 !rx_done_tick);

  // Minimal functional coverage
  cover property (state_reg==idle && rx_en && fall_edge);      // start detected
  cover property (state_reg==dps && fall_edge && n_reg==0);    // last edge before load
  cover property (rx_done_tick);                               // byte complete

endmodule

bind ps2_rx ps2_rx_sva sva (
  .clk(clk), .reset(reset), .ps2d(ps2d), .ps2c(ps2c), .rx_en(rx_en),
  .rx_done_tick(rx_done_tick), .dout(dout),
  .state_reg(state_reg), .filter_reg(filter_reg), .f_ps2c_reg(f_ps2c_reg),
  .n_reg(n_reg), .b_reg(b_reg), .fall_edge(fall_edge)
);

`endif
// SVA for ps2_rx. Bind this file to the DUT.
module ps2_rx_sva (
  input logic         clk, reset,
  input logic         ps2d, ps2c, rx_en,
  input logic         rx_done_tick,
  input logic [7:0]   dout,
  input logic [1:0]   state_reg,
  input logic [3:0]   n_reg,
  input logic [10:0]  b_reg,
  input logic [7:0]   filter_reg, filter_next,
  input logic         f_ps2c_reg, f_ps2c_next,
  input logic         fall_edge
);
  localparam logic [1:0] idle=2'b00, dps=2'b01, load=2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Reset post-conditions (checked on first clk after reset rises)
  assert property (@(posedge clk) disable iff (1'b0)
    $rose(reset) |=> (state_reg==idle && n_reg==0 && b_reg==0 && filter_reg==0 && f_ps2c_reg==0));

  // Debounce/filter pipeline correctness
  assert property (filter_reg == $past(filter_next));
  assert property (f_ps2c_reg == $past(f_ps2c_next));
  assert property (($past(filter_reg)==8'hFF) |->  f_ps2c_reg);
  assert property (($past(filter_reg)==8'h00) |-> !f_ps2c_reg);
  assert property (($past(filter_reg)!=8'hFF && $past(filter_reg)!=8'h00) |-> f_ps2c_reg==$past(f_ps2c_reg));
  assert property (fall_edge |-> f_ps2c_reg && ##1 !f_ps2c_reg);
  assert property (fall_edge |-> ##1 !fall_edge); // single-cycle pulse

  // Output mapping always matches
  assert property (dout == b_reg[8:1]);

  // State encoding valid
  assert property (state_reg inside {idle,dps,load});

  // Idle behavior
  assert property ((state_reg==idle && !(fall_edge && rx_en))
                   |-> ##1 (state_reg==idle && n_reg==$past(n_reg) && b_reg==$past(b_reg)));
  assert property ((state_reg==idle && fall_edge && rx_en)
                   |-> ##1 (state_reg==dps && n_reg==4'd9 &&
                            b_reg=={ $past(ps2d), $past(b_reg[10:1])}));
  assert property ((state_reg==idle && fall_edge && !rx_en)
                   |-> ##1 (state_reg==idle && n_reg==$past(n_reg) && b_reg==$past(b_reg)));

  // DPS behavior
  assert property ((state_reg==dps && !fall_edge)
                   |-> ##1 (state_reg==dps && n_reg==$past(n_reg) && b_reg==$past(b_reg)));
  assert property ((state_reg==dps && fall_edge && n_reg>0)
                   |-> ##1 (state_reg==dps && n_reg==$past(n_reg)-1 &&
                            b_reg=={ $past(ps2d), $past(b_reg[10:1])}));
  assert property ((state_reg==dps && fall_edge && n_reg==0)
                   |-> ##1 (state_reg==load && n_reg==$past(n_reg) &&
                            b_reg=={ $past(ps2d), $past(b_reg[10:1])}));

  // LOAD behavior and rx_done_tick pulse semantics
  assert property (state_reg==load |-> (rx_done_tick && ##1 state_reg==idle));
  assert property (rx_done_tick |-> state_reg==load);
  assert property (rx_done_tick |-> ##1 !rx_done_tick);

  // Completion: a frame start leads to a done tick after 10 filtered falling edges
  sequence start_evt; (state_reg==idle && fall_edge && rx_en); endsequence
  sequence dps_fall;  (state_reg==dps && fall_edge); endsequence
  assert property (start_evt |-> ##1 dps_fall[->10] ##1 (state_reg==load && rx_done_tick) ##1 (state_reg==idle));

  // X/Z checks on key state
  assert property (!$isunknown({state_reg,n_reg,b_reg,filter_reg,f_ps2c_reg,rx_done_tick,dout}));

  // Coverage
  cover property (start_evt ##1 dps_fall[->10] ##1 rx_done_tick);
  cover property ((filter_reg==8'hFF) ##1 f_ps2c_reg && fall_edge==0);
  cover property ((filter_reg==8'h00) ##1 !f_ps2c_reg && fall_edge==0);
  cover property (start_evt ##1 dps_fall[->10] ##1 rx_done_tick ##[5:100] start_evt ##1 dps_fall[->10] ##1 rx_done_tick);
endmodule

bind ps2_rx ps2_rx_sva sva_ps2_rx (
  .clk(clk), .reset(reset),
  .ps2d(ps2d), .ps2c(ps2c), .rx_en(rx_en),
  .rx_done_tick(rx_done_tick), .dout(dout),
  .state_reg(state_reg), .n_reg(n_reg), .b_reg(b_reg),
  .filter_reg(filter_reg), .filter_next(filter_next),
  .f_ps2c_reg(f_ps2c_reg), .f_ps2c_next(f_ps2c_next),
  .fall_edge(fall_edge)
);
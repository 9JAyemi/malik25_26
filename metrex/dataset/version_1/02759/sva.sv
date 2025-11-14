// SVA for synth_arb. Bind this file to the DUT.
// Focused, concise checks of state machine, outputs, waits, wreq_inter/w_done handshake, and d2ctrl_synth mapping.

module synth_arb_sva (
  input  logic        clk, reset_n, fifo_full,
  input  logic        wreq_inter, w_done,
  input  logic [7:0]  memadrs, memdata,
  input  logic [7:0]  synth_ctrl, synth_data,
  input  logic [7:0]  state_reg,
  input  logic [3:0]  wait_cnt
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Reset drives known values
  assert property (!reset_n |-> state_reg==8'd0 && synth_ctrl==8'h00 && synth_data==8'h00
                              && wait_cnt==4'h0 && w_done==1'b0 && wreq_inter==1'b0);

  // State encoding stays within 0..8
  assert property (state_reg inside {8'd0,8'd1,8'd2,8'd3,8'd4,8'd5,8'd6,8'd7,8'd8});

  // State transitions and outputs by state
  assert property (state_reg==8'd0 |=> state_reg==8'd1);

  assert property (state_reg==8'd1 && wait_cnt!=4'hF |=> state_reg==8'd1 && wait_cnt==$past(wait_cnt)+1);
  assert property (state_reg==8'd1 && wait_cnt==4'hF |=> state_reg==8'd2 && wait_cnt==4'hF);

  assert property (state_reg==8'd2 |-> synth_ctrl==8'h01);
  assert property (state_reg==8'd2 |=> state_reg==8'd3);

  assert property (state_reg==8'd3 |-> synth_ctrl==8'h00);
  assert property (state_reg==8'd3 && fifo_full |=> state_reg==8'd3);
  assert property (state_reg==8'd3 && !fifo_full |=> state_reg==8'd4);

  assert property (state_reg==8'd4 |-> synth_ctrl==8'h81);
  assert property (state_reg==8'd4 |=> state_reg==8'd5);

  assert property (state_reg==8'd5 |-> synth_ctrl==8'h00);
  assert property (state_reg==8'd5 |=> state_reg==8'd6);

  assert property (state_reg==8'd6 && wreq_inter |=> state_reg==8'd7);
  assert property (state_reg==8'd6 && !wreq_inter |=> state_reg==8'd2);

  assert property (state_reg==8'd7 |-> w_done && synth_data==memdata);
  assert property (state_reg==8'd7 |=> state_reg==8'd8);

  assert property (state_reg==8'd8 |-> synth_ctrl==8'h00 && !w_done);
  assert property (state_reg==8'd8 |=> state_reg==8'd2);

  // d2ctrl_synth mapping checks (in state 7)
  assert property ((state_reg==8'd7 && memadrs==8'h01) |-> synth_ctrl==8'h41);
  assert property ((state_reg==8'd7 && memadrs==8'h11) |-> synth_ctrl==8'h11);
  assert property ((state_reg==8'd7 && memadrs==8'h21) |-> synth_ctrl==8'h51);
  assert property ((state_reg==8'd7 && memadrs[7:4]==4'h8) |-> synth_ctrl==8'h20);
  assert property ((state_reg==8'd7 && !(memadrs==8'h01 || memadrs==8'h11 || memadrs==8'h21 || memadrs[7:4]==4'h8))
                   |-> synth_ctrl==8'h00);

  // w_done one-cycle pulse, only asserted in state 7
  assert property ($rose(w_done) |-> $past(state_reg)==8'd7);
  assert property (w_done |-> state_reg==8'd7);
  assert property ($rose(w_done) |=> !w_done); // 1-cycle high

  // wreq_inter lifecycle: once set, it stays until w_done or reset; cleared after w_done
  assert property (wreq_inter && !w_done |-> (wreq_inter until_with (w_done || !reset_n)));
  assert property ($rose(w_done) |=> !wreq_inter);

  // Wait counter only changes in state 1 before hitting 0xF
  assert property ($changed(wait_cnt) |-> $past(state_reg)==8'd1 && $past(wait_cnt)!=4'hF);

  // synth_data only updates in state 7
  assert property ($changed(synth_data) |-> $past(state_reg)==8'd7);

  // Coverage
  cover property (state_reg==8'd2 ##1 state_reg==8'd3 ##1 state_reg==8'd4 ##1 state_reg==8'd5
                  ##1 state_reg==8'd6 ##1 state_reg==8'd7 ##1 state_reg==8'd8 ##1 state_reg==8'd2);

  cover property (state_reg==8'd3 && fifo_full ##1 state_reg==8'd3 && !fifo_full ##1 state_reg==8'd4);

  cover property (state_reg==8'd6 && !wreq_inter ##1 state_reg==8'd2);
  cover property (state_reg==8'd6 && wreq_inter  ##1 state_reg==8'd7);

  cover property (state_reg==8'd7 && memadrs==8'h01);
  cover property (state_reg==8'd7 && memadrs==8'h11);
  cover property (state_reg==8'd7 && memadrs==8'h21);
  cover property (state_reg==8'd7 && memadrs[7:4]==4'h8);

endmodule

bind synth_arb synth_arb_sva i_synth_arb_sva (.*);
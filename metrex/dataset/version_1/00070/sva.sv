// SVA for ctrl_reg_readback
// Bindable, concise, and coverage-oriented

module ctrl_reg_readback_sva #(parameter CR_WIDTH=6, N_CTRL_REGS=64) (
  input  logic                    clk,
  input  logic                    rst,
  input  logic                    tx_en,
  input  logic                    tx_data_loaded,
  input  logic [CR_WIDTH-1:0]     tx_cnt,
  input  logic                    tx_data_ready,
  input  logic                    tx_complete
);

  // Sanity on parameters (time 0, compile-time constants)
  initial begin
    assert (N_CTRL_REGS > 0);
    assert (N_CTRL_REGS <= (1<<CR_WIDTH));
  end

  localparam int unsigned LAST = N_CTRL_REGS-1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpful sequences
  sequence handshake; (!tx_complete && tx_en && tx_data_ready && tx_data_loaded); endsequence
  sequence ready_req; (!tx_complete && tx_en && !tx_data_ready && !tx_data_loaded); endsequence

  // Reset behavior (synchronous)
  a_reset:                  assert property (rst |=> (tx_cnt==0 && tx_data_ready==0 && tx_complete==0));

  // Known/clean outputs
  a_known_outs:             assert property (!$isunknown({tx_cnt, tx_data_ready, tx_complete}));

  // Input sanity when used
  a_known_loaded_when_used: assert property ((!tx_complete && tx_en) |-> !$isunknown(tx_data_loaded));

  // Counter range never exceeds LAST
  a_cnt_range:              assert property (tx_cnt <= LAST);

  // Ready rise/fall legality and requirement
  a_ready_rises_only_on_req: assert property ($rose(tx_data_ready) |-> $past(ready_req));
  a_ready_must_rise_on_req:  assert property ($past(ready_req) |-> tx_data_ready);
  a_ready_falls_only_by_hs_or_clear:
                             assert property ($fell(tx_data_ready) |-> $past(handshake || (tx_complete && !tx_en)));

  // Counter update rules
  a_cnt_inc_on_hs:          assert property ($past(handshake && ($past(tx_cnt) != LAST)) |-> (tx_cnt == $past(tx_cnt)+1 && !tx_complete));
  a_cnt_hold_on_last_hs:    assert property ($past(handshake && ($past(tx_cnt) == LAST)) |-> (tx_cnt == $past(tx_cnt) && tx_complete));
  a_cnt_stable_no_hs:       assert property ($past(!handshake && !(tx_complete && !tx_en)) |-> tx_cnt == $past(tx_cnt));

  // Completion flag rules
  a_complete_rise_only_on_last_hs:
                             assert property ($rose(tx_complete) |-> $past(handshake && ($past(tx_cnt)==LAST)));
  a_complete_holds_with_en: assert property ((tx_complete && tx_en) |=> ($stable(tx_complete) && $stable(tx_cnt) && $stable(tx_data_ready)));
  a_complete_clears_only_on_en_low:
                             assert property ($fell(tx_complete) |-> $past(tx_complete && !tx_en));
  a_clear_after_done_and_en_low:
                             assert property ($past(tx_complete && !tx_en) |-> (tx_complete==0 && tx_cnt==0 && tx_data_ready==0));

  // Ready must be 0 whenever complete is 1
  a_ready_zero_when_complete: assert property (tx_complete |-> (tx_data_ready==0));

  // Hold when idle (not complete and not enabled)
  a_stable_when_idle:        assert property ((!tx_complete && !tx_en) |=> $stable({tx_cnt, tx_complete, tx_data_ready}));

  // Coverage
  c_ready_req_then_hs:       cover property (ready_req ##1 tx_data_ready ##1 (tx_data_ready && tx_data_loaded) ##1 !tx_data_ready);
  c_single_inc:              cover property ($rose(tx_data_ready) ##1 (tx_data_ready && tx_data_loaded) ##1 (tx_cnt == $past(tx_cnt)+1));
  c_full_readback:           cover property (tx_en && !tx_complete ##1 (handshake)[*N_CTRL_REGS] ##1 tx_complete);
  c_complete_then_clear:     cover property (tx_complete ##1 !tx_en ##1 (!tx_complete && tx_cnt==0 && tx_data_ready==0));

endmodule

// Bind into DUT
bind ctrl_reg_readback
  ctrl_reg_readback_sva #(.CR_WIDTH(CR_WIDTH), .N_CTRL_REGS(N_CTRL_REGS)) u_ctrl_reg_readback_sva (
    .clk(clk),
    .rst(rst),
    .tx_en(tx_en),
    .tx_data_loaded(tx_data_loaded),
    .tx_cnt(tx_cnt),
    .tx_data_ready(tx_data_ready),
    .tx_complete(tx_complete)
  );
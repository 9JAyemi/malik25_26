// SVA for prometheus_fx3_partial
// Bind into the DUT; uses internal signals via bind port connections.

module prometheus_fx3_partial_sva
  #(parameter [2:0] STATE_IDLE            = 3'd0,
              [2:0] STATE_WAIT_FLAGB     = 3'd1,
              [2:0] STATE_WRITE          = 3'd2,
              [2:0] STATE_WRITE_WR_DELAY = 3'd3,
              [2:0] STATE_WAIT           = 3'd4)
(
  input  logic        clk_100,
  input  logic        rst_n,

  // DUT ports
  input  logic        partial_mode_selected,
  input  logic        i_gpif_in_ch0_rdy_d,
  input  logic        i_gpif_out_ch0_rdy_d,
  input  logic        o_gpif_we_n_partial_,
  input  logic        o_gpif_pkt_end_n_partial_,
  input  logic [31:0] data_out_partial,

  // DUT internals
  input  logic [2:0]  current_partial_state,
  input  logic [2:0]  next_partial_state,
  input  logic [3:0]  strob_cnt,
  input  logic        strob,
  input  logic [3:0]  short_pkt_cnt,
  input  logic [31:0] data_gen_partial,
  input  logic        o_gpif_pkt_end_n_prtl_
);

  default clocking cb @(posedge clk_100); endclocking
  default disable iff (!rst_n);

  // State validity and registration
  assert property (current_partial_state inside {STATE_IDLE,STATE_WAIT_FLAGB,STATE_WRITE,STATE_WRITE_WR_DELAY,STATE_WAIT});
  assert property (next_partial_state    inside {STATE_IDLE,STATE_WAIT_FLAGB,STATE_WRITE,STATE_WRITE_WR_DELAY,STATE_WAIT});
  assert property (current_partial_state == $past(next_partial_state));

  // Next-state function correctness (combinational)
  assert property (current_partial_state == STATE_IDLE |->
                   next_partial_state == ( (partial_mode_selected && i_gpif_in_ch0_rdy_d) ? STATE_WAIT_FLAGB : STATE_IDLE ));

  assert property (current_partial_state == STATE_WAIT_FLAGB |->
                   next_partial_state == ( i_gpif_out_ch0_rdy_d ? STATE_WRITE : STATE_WAIT_FLAGB ));

  assert property (current_partial_state == STATE_WRITE |->
                   next_partial_state == ( (!i_gpif_out_ch0_rdy_d || (strob && short_pkt_cnt==4'hF)) ? STATE_WRITE_WR_DELAY : STATE_WRITE ));

  assert property (current_partial_state == STATE_WRITE_WR_DELAY |->
                   next_partial_state == STATE_WAIT);

  assert property (current_partial_state == STATE_WAIT |->
                   next_partial_state == ( strob_cnt==4'd7 ? STATE_IDLE : STATE_WAIT ));

  // Counters behavior
  assert property (current_partial_state == STATE_IDLE |-> (short_pkt_cnt==4'd0 && strob_cnt==4'd0));

  assert property (current_partial_state == STATE_WRITE |=> short_pkt_cnt == $past(short_pkt_cnt)+1);
  assert property ((current_partial_state != STATE_WRITE) && (current_partial_state != STATE_IDLE) |=> $stable(short_pkt_cnt));

  assert property (current_partial_state == STATE_WAIT |=> strob_cnt == $past(strob_cnt)+1);
  assert property ((current_partial_state != STATE_WAIT) && (current_partial_state != STATE_IDLE) |=> $stable(strob_cnt));

  // Strobe behavior
  assert property ((current_partial_state == STATE_WAIT && strob_cnt==4'd7) |=> strob == !$past(strob));
  assert property (!(current_partial_state == STATE_WAIT && strob_cnt==4'd7) |=> $stable(strob));

  // Write enable definition
  assert property (o_gpif_we_n_partial_ == !(current_partial_state==STATE_WRITE && i_gpif_out_ch0_rdy_d));

  // Packet end definition and consistency
  assert property (o_gpif_pkt_end_n_partial_ == o_gpif_pkt_end_n_prtl_);
  assert property (o_gpif_pkt_end_n_partial_ == !(partial_mode_selected && strob && short_pkt_cnt==4'hF));

  // If WRITE terminates due to short-packet condition, pkt_end must assert that cycle
  assert property (current_partial_state==STATE_WRITE && strob && short_pkt_cnt==4'hF |->
                   next_partial_state==STATE_WRITE_WR_DELAY && o_gpif_pkt_end_n_partial_==1'b0);

  // Data generator behavior
  assert property (data_out_partial == data_gen_partial);
  assert property (partial_mode_selected && (o_gpif_we_n_partial_==1'b0) |=> data_gen_partial == $past(data_gen_partial)+1);
  assert property (partial_mode_selected && (o_gpif_we_n_partial_==1'b1) |=> $stable(data_gen_partial));
  assert property (!partial_mode_selected |=> data_gen_partial == 32'd0);

  // Simple X-check on outputs (post-reset)
  assert property (!$isunknown({o_gpif_we_n_partial_, o_gpif_pkt_end_n_partial_}));

  // Coverage
  cover property (current_partial_state==STATE_IDLE ##1
                  current_partial_state==STATE_WAIT_FLAGB ##1
                  current_partial_state==STATE_WRITE ##1
                  current_partial_state==STATE_WRITE_WR_DELAY ##1
                  current_partial_state==STATE_WAIT ##1
                  current_partial_state==STATE_IDLE);

  cover property (current_partial_state==STATE_WRITE && i_gpif_out_ch0_rdy_d && o_gpif_we_n_partial_==1'b0);
  cover property (current_partial_state==STATE_WRITE && short_pkt_cnt==4'hF);
  cover property (partial_mode_selected && strob && short_pkt_cnt==4'hF && o_gpif_pkt_end_n_partial_==1'b0);
  cover property (current_partial_state==STATE_WAIT && strob_cnt==4'd7 ##1 $changed(strob));

endmodule

// Bind into all instances of the DUT. Parameters are sourced from DUT's params.
bind prometheus_fx3_partial prometheus_fx3_partial_sva
  #(.STATE_IDLE(partial_idle),
    .STATE_WAIT_FLAGB(partial_wait_flagb),
    .STATE_WRITE(partial_write),
    .STATE_WRITE_WR_DELAY(partial_write_wr_delay),
    .STATE_WAIT(partial_wait))
(
  .clk_100(clk_100),
  .rst_n(rst_n),

  .partial_mode_selected(partial_mode_selected),
  .i_gpif_in_ch0_rdy_d(i_gpif_in_ch0_rdy_d),
  .i_gpif_out_ch0_rdy_d(i_gpif_out_ch0_rdy_d),
  .o_gpif_we_n_partial_(o_gpif_we_n_partial_),
  .o_gpif_pkt_end_n_partial_(o_gpif_pkt_end_n_partial_),
  .data_out_partial(data_out_partial),

  .current_partial_state(current_partial_state),
  .next_partial_state(next_partial_state),
  .strob_cnt(strob_cnt),
  .strob(strob),
  .short_pkt_cnt(short_pkt_cnt),
  .data_gen_partial(data_gen_partial),
  .o_gpif_pkt_end_n_prtl_(o_gpif_pkt_end_n_prtl_)
);
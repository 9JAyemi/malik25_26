// SVA for non_posted_pkt_builder
// Bind this module to the DUT:
// bind non_posted_pkt_builder non_posted_pkt_builder_sva svainst();

module non_posted_pkt_builder_sva;

  // Clock/reset context
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst_reg);

  // Mirror DUT encodings/constants
  localparam IDLE  = 4'h0;
  localparam HEAD1 = 4'h1;
  localparam HEAD2 = 4'h2;
  localparam WAIT_FOR_GO_DEASSERT = 4'h3;

  localparam rsvd=1'b0, MRd=5'b00000, TC=3'b000, TD=1'b0, EP=1'b0, ATTR=2'b00, LastBE=4'b1111, FirstBE=4'b1111;

  // Basic reset behavior
  ap_reset_outputs: assert property (rst_reg |-> state==IDLE &&
                                     header_data_out==64'b0 &&
                                     header_data_wren==1'b0 &&
                                     ack==1'b0 && tag_inc==1'b0 &&
                                     tx_waddr==5'b0 && tx_wdata==32'b0 && tx_we==1'b0);

  // fmt correctness w.r.t. registered DMA read address
  ap_fmt_def: assert property (fmt == ((dmaras_reg[63:32]==32'b0) ? 2'b00 : 2'b01));

  // FSM transitions
  ap_idle_stay:      assert property ($past(state)==IDLE  && !$past(go)     |-> state==IDLE);
  ap_idle_to_head1:  assert property ($past(state)==IDLE  &&  $past(go)     |-> state==HEAD1);

  ap_head1_stay:     assert property ($past(state)==HEAD1 && !$past(tag_gnt) |-> state==HEAD1 && header_data_wren==1'b0);
  ap_head1_to_head2: assert property ($past(state)==HEAD1 &&  $past(tag_gnt) |-> state==HEAD2 && header_data_wren==1'b1);

  ap_head2_to_wait:  assert property ($past(state)==HEAD2 |-> state==WAIT_FOR_GO_DEASSERT);
  ap_wait_to_idle:   assert property ($past(state)==WAIT_FOR_GO_DEASSERT |-> state==IDLE);

  // Ensures HEAD2 only reached with tag grant
  ap_head2_requires_grant: assert property ($past(state)==HEAD1 && state==HEAD2 |-> $past(tag_gnt));

  // Capture of DMA regs on go when leaving IDLE
  ap_capture_regs_on_go: assert property ($past(state)==IDLE && state==HEAD1 |->
                                          $past(go) &&
                                          dmaras_reg==$past(dmaras) &&
                                          dmarad_reg==$past(dmarad));

  // header_data_out contents in HEAD1 (checked in the cycle it was driven)
  ap_head1_header_word: assert property ($past(state)==HEAD1 |->
    $past(header_data_out) == {rsvd, $past(fmt), MRd, rsvd, TC, rsvd,rsvd,rsvd,rsvd,
                               TD, EP, ATTR, rsvd, rsvd, $past(length[9:0]), $past(req_id[15:0]),
                               $past(tag_value[7:0]), LastBE, FirstBE});

  // header_data_out contents in HEAD2 depend on fmt[0]
  ap_head2_hdr_64: assert property (state==HEAD2 && fmt[0]==1'b1 |->
                                    header_data_out=={dmaras_reg[63:2],2'b00});
  ap_head2_hdr_32: assert property (state==HEAD2 && fmt[0]==1'b0 |->
                                    header_data_out=={dmaras_reg[31:2],2'b00, dmaras_reg[63:32]});

  // WREN behavior
  ap_wren_usage: assert property (header_data_wren |-> (state==HEAD2) ||
                                                ($past(state)==HEAD1 && $past(tag_gnt)));
  ap_wren_zero_outside: assert property ((state==IDLE || state==WAIT_FOR_GO_DEASSERT) |-> header_data_wren==1'b0);

  // ACK/TAG_INC behavior
  ap_ack_only_head2: assert property (ack |-> state==HEAD2);
  ap_taginc_only_head2: assert property (tag_inc |-> state==HEAD2);
  ap_head2_flags: assert property (state==HEAD2 |-> ack && tag_inc);
  ap_ack_one_cycle: assert property ($rose(ack) |-> ##1 !ack);

  // TX write side-effects only in HEAD2
  ap_txwe_only_head2: assert property (tx_we |-> state==HEAD2);
  ap_txwe_in_head2:   assert property (state==HEAD2 |-> tx_we==1'b1);
  ap_txaddr_in_head2: assert property (state==HEAD2 |-> tx_waddr==tag_value[4:0]);
  ap_txdata_in_head2: assert property (state==HEAD2 |-> tx_wdata=={isDes,9'b0, dmarad_reg[27:6]});

  // No X/Z on key outputs/state when not in reset
  ap_no_x: assert property (!$isunknown({state, ack, tag_inc, header_data_wren, tx_we, tx_waddr, tx_wdata, header_data_out}));

  // Coverage
  cv_full_flow_64: cover property (state==IDLE ##1 go ##1 state==HEAD1 ##1 tag_gnt ##1
                                   state==HEAD2 && fmt[0]==1'b1 ##1 state==WAIT_FOR_GO_DEASSERT ##1 state==IDLE);
  cv_full_flow_32: cover property (state==IDLE ##1 go ##1 state==HEAD1 ##1 tag_gnt ##1
                                   state==HEAD2 && fmt[0]==1'b0 ##1 state==WAIT_FOR_GO_DEASSERT ##1 state==IDLE);
  cv_head1_stall_then_grant: cover property (state==HEAD1 && !tag_gnt ##1 state==HEAD1 && !tag_gnt ##1
                                             state==HEAD1 && tag_gnt ##1 state==HEAD2);
  cv_ack_pulse: cover property ($rose(ack));

endmodule
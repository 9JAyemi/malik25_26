// SVA for mc_ctrl. Bind into the DUT.
// Focus: FSM integrity, legal transitions, outputs equivalence, handshakes, and concise coverage.

module mc_ctrl_sva (
  input  logic         clk,
  input  logic         rstn,
  input  logic         mc_start_i,
  input  logic         mc_done_o,
  input  logic         mvd_access_o,
  input  logic         chroma_start_o,
  input  logic         chroma_sel_o,
  input  logic         chroma_done_i,
  input  logic         tq_start_o,
  input  logic         tq_done_i,
  input  logic [1:0]   tq_sel_o,
  input  logic [2:0]   current_state,
  input  logic [2:0]   next_state
);

  localparam IDLE    = 3'd0;
  localparam TQ_LUMA = 3'd1;
  localparam MC_CB   = 3'd2;
  localparam TQ_CB   = 3'd3;
  localparam MC_CR   = 3'd4;
  localparam TQ_CR   = 3'd5;
  localparam DONE    = 3'd6;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rstn)

  // Basic sanity
  a_no_x:          assert property (!$isunknown({current_state,next_state,mc_done_o,mvd_access_o,chroma_start_o,chroma_sel_o,tq_start_o,tq_sel_o})));
  a_state_follow:  assert property ($past(rstn) |-> current_state == $past(next_state));
  // Async reset drives IDLE (checked even during reset)
  a_reset_idles:   assert property (@(posedge clk) !rstn |-> current_state == IDLE);

  // Legal state progress (hold/advance)
  a_idle_hold:     assert property (current_state==IDLE    && !mc_start_i  |=> current_state==IDLE);
  a_idle_to_tq:    assert property (current_state==IDLE    &&  mc_start_i  |=> current_state==TQ_LUMA);

  a_tql_hold:      assert property (current_state==TQ_LUMA && !tq_done_i   |=> current_state==TQ_LUMA);
  a_tql_to_mccb:   assert property (current_state==TQ_LUMA &&  tq_done_i   |=> current_state==MC_CB);

  a_mccb_hold:     assert property (current_state==MC_CB   && !chroma_done_i |=> current_state==MC_CB);
  a_mccb_to_tqcb:  assert property (current_state==MC_CB   &&  chroma_done_i |=> current_state==TQ_CB);

  a_tqcb_hold:     assert property (current_state==TQ_CB   && !tq_done_i   |=> current_state==TQ_CB);
  a_tqcb_to_mccr:  assert property (current_state==TQ_CB   &&  tq_done_i   |=> current_state==MC_CR);

  a_mccr_hold:     assert property (current_state==MC_CR   && !chroma_done_i |=> current_state==MC_CR);
  a_mccr_to_tqcr:  assert property (current_state==MC_CR   &&  chroma_done_i |=> current_state==TQ_CR);

  a_tqcr_hold:     assert property (current_state==TQ_CR   && !tq_done_i   |=> current_state==TQ_CR);
  a_tqcr_to_done:  assert property (current_state==TQ_CR   &&  tq_done_i   |=> current_state==DONE);

  a_done_to_idle:  assert property (current_state==DONE                   |=> current_state==IDLE);

  // Output equivalences
  a_mc_done_o:     assert property (mc_done_o == (current_state==DONE));
  a_mvd_access_o:  assert property (mvd_access_o == (current_state==TQ_LUMA));
  a_chroma_sel_o:  assert property (chroma_sel_o == (current_state==MC_CR));

  // tq_sel_o mapping and validity
  a_tq_sel_map:    assert property (
                      (current_state==TQ_LUMA && tq_sel_o==2'b00) ||
                      (current_state==TQ_CB   && tq_sel_o==2'b10) ||
                      (current_state==TQ_CR   && tq_sel_o==2'b11) ||
                      ((current_state inside {IDLE,MC_CB,MC_CR,DONE}) && tq_sel_o==2'b00)
                    );
  a_tq_sel_valid:  assert property (tq_sel_o != 2'b01);

  // Start pulse mappings (combinational next_state-based)
  a_chroma_start:  assert property (chroma_start_o ==
                      ((current_state==TQ_LUMA && next_state==MC_CB) ||
                       (current_state==TQ_CB   && next_state==MC_CR)));
  a_tq_start:      assert property (tq_start_o ==
                      ((current_state==IDLE    && next_state==TQ_LUMA) ||
                       (current_state==MC_CB   && next_state==TQ_CB)   ||
                       (current_state==MC_CR   && next_state==TQ_CR)));
  a_start_no_overlap: assert property (!(tq_start_o && chroma_start_o));

  // DONE behavior
  a_done_props:    assert property ((current_state==DONE) |-> (mc_done_o && next_state==IDLE));

  // Coverage
  c_visit_all_states: cover property ( (current_state==IDLE) ##1
                                       (current_state==TQ_LUMA) ##1
                                       (current_state==MC_CB) ##1
                                       (current_state==TQ_CB) ##1
                                       (current_state==MC_CR) ##1
                                       (current_state==TQ_CR) ##1
                                       (current_state==DONE) );

  c_full_flow: cover property (
                 (current_state==IDLE && mc_start_i) ##1
                 (current_state==TQ_LUMA) ##[1:$]
                 (current_state==MC_CB)  ##[1:$]
                 (current_state==TQ_CB)  ##[1:$]
                 (current_state==MC_CR)  ##[1:$]
                 (current_state==TQ_CR)  ##[1:$]
                 (current_state==DONE)   ##1
                 (current_state==IDLE)
               );

  c_start_pulses: cover property (tq_start_o);
  c_chroma_pulses: cover property (chroma_start_o);
  c_chroma_sel_1: cover property (chroma_sel_o);
  c_tq_sel_00: cover property (tq_sel_o==2'b00);
  c_tq_sel_10: cover property (tq_sel_o==2'b10);
  c_tq_sel_11: cover property (tq_sel_o==2'b11);

endmodule

bind mc_ctrl mc_ctrl_sva u_mc_ctrl_sva (
  .clk(clk),
  .rstn(rstn),
  .mc_start_i(mc_start_i),
  .mc_done_o(mc_done_o),
  .mvd_access_o(mvd_access_o),
  .chroma_start_o(chroma_start_o),
  .chroma_sel_o(chroma_sel_o),
  .chroma_done_i(chroma_done_i),
  .tq_start_o(tq_start_o),
  .tq_done_i(tq_done_i),
  .tq_sel_o(tq_sel_o),
  .current_state(current_state),
  .next_state(next_state)
);
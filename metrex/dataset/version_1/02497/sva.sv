// SVA for sample_generator
// Bind this module to the DUT:  bind sample_generator sample_generator_sva u_sva();

module sample_generator_sva;

  // Access bound instance scope symbols directly
  localparam int IDLE=0, START=1, DATA=2, END=3;

  default clocking cb @(posedge m_axis_aclk); endclocking
  default disable iff (!m_axis_aresetn);

  // Shorthands
  let hs          = m_axis_tvalid && m_axis_tready;
  let last_hs     = hs && m_axis_tlast;
  let non_last_hs = hs && !m_axis_tlast;
  let nbeats      = (FrameSize + 8'd3) >> 2;  // ceil(FrameSize/4)

  // 1) Reset and state encoding
  assert property (!m_axis_aresetn |-> (state==IDLE && frame_count==0 && data_count==0 &&
                                        m_axis_tvalid==0 && m_axis_tlast==0 &&
                                        m_axis_tstrb==4'h0 && m_axis_tdata==32'h0 &&
                                        s_axis_tready==0));
  assert property (state inside {IDLE,START,DATA,END});

  // 2) Ready mapping and valid rules
  assert property ((state==DATA) -> (s_axis_tready==m_axis_tready));
  assert property ((state!=DATA) -> (s_axis_tready==1'b0));
  assert property ((state==IDLE) -> !m_axis_tvalid);
  assert property ((state!=IDLE) ->  m_axis_tvalid);

  // 3) AXI-Stream protocol: stability under backpressure, last with valid, no Xs
  assert property (m_axis_tvalid && !m_axis_tready |-> $stable({m_axis_tdata,m_axis_tstrb,m_axis_tlast}));
  assert property (m_axis_tlast -> m_axis_tvalid);
  assert property (m_axis_tvalid |-> !$isunknown({m_axis_tdata,m_axis_tstrb,m_axis_tlast,m_axis_tready}));

  // 4) Data/strb semantics on handshakes
  assert property (hs -> (m_axis_tstrb==4'hF));
  assert property (m_axis_tvalid -> (m_axis_tdata[1:0]==2'b00)); // word aligned

  // 5) Last only in END, END holds valid/last until accepted
  assert property (m_axis_tlast -> (state==END));
  assert property ((state==END) -> (m_axis_tvalid && m_axis_tlast));

  // 6) First beat data = 0
  sequence start_from_idle; $past(state)==IDLE && state==START; endsequence
  assert property (start_from_idle && (nbeats>0) |-> ##[1:$] (non_last_hs && m_axis_tdata==32'd0));
  assert property (start_from_idle && (nbeats==0) |-> ##[1:$] (last_hs && m_axis_tdata==32'd0));

  // 7) Increment by 4 per accepted beat within a frame
  property p_inc_by4_between_handshakes;
    int d;
    (non_last_hs, d=m_axis_tdata) |-> ##[1:$] (hs && m_axis_tdata==(d+32'd4)) until_with last_hs;
  endproperty
  assert property (p_inc_by4_between_handshakes);

  // 8) Frame length matches FrameSize (beats = ceil(FrameSize/4))
  assert property (start_from_idle && (nbeats==0) |-> ##[1:$] last_hs);
  assert property (start_from_idle && (nbeats>0)  |-> ##[1:$] non_last_hs[* (nbeats-1)] ##1 last_hs);

  // 9) Post-last state transition as specified
  assert property (last_hs |-> ##1 ((frame_count==8'hFF) ? (state==IDLE) : (state==START)));

  // 10) Coverage
  cover property (start_from_idle ##[1:$] non_last_hs[*1:$] ##1 last_hs ##1 state==START);
  cover property (m_axis_tvalid && !m_axis_tready [*3] ##1 hs);
  cover property (frame_count==8'hFF ##1 last_hs ##1 state==IDLE);

endmodule
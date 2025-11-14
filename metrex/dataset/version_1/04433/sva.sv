// SVA for axis_bayer_extractor
// Drop into the module or bind; uses generate labels as given (direct_connect/extract_quater)

`ifdef AXIS_BAYER_EXTRACTOR_SVA
default clocking cb @(posedge clk); endclocking
default disable iff (!resetn);

wire snext = s_axis_tvalid && s_axis_tready;
wire mnext = m_axis_tvalid && m_axis_tready;

generate
if (C_BYPASS==1) begin : sva_bypass
  // Pure pass-through equivalence
  assert property (s_axis_tvalid == m_axis_tvalid);
  assert property (s_axis_tdata  == m_axis_tdata);
  assert property (s_axis_tuser  == m_axis_tuser);
  assert property (s_axis_tlast  == m_axis_tlast);
  assert property (s_axis_tready == m_axis_tready);

  // Basic coverage
  cover property (snext);
  cover property (mnext);
  cover property (snext && s_axis_tuser);
  cover property (snext && s_axis_tlast);
end else begin : sva_extract

  // Ready expression
  assert property (s_axis_tready == (!m_axis_tvalid || m_axis_tready));

  // Valid must hold and payload must be stable under backpressure
  assert property (m_axis_tvalid && !m_axis_tready |=> m_axis_tvalid && $stable(m_axis_tdata) && $stable(m_axis_tlast) && $stable(m_axis_tuser) until_with m_axis_tready);

  // Valid clears on ready
  assert property (m_axis_tvalid && m_axis_tready |=> !m_axis_tvalid);

  // No input accept while output is stalled
  assert property (m_axis_tvalid && !m_axis_tready |-> !snext);

  // Internal toggle checks
  assert property (snext |=> extract_quater.spixel_lsb == !$past(extract_quater.spixel_lsb));
  assert property (snext && s_axis_tlast |=> extract_quater.sline_lsb == !$past(extract_quater.sline_lsb));
  assert property (snext && !s_axis_tlast |=> extract_quater.sline_lsb ==  $past(extract_quater.sline_lsb));

  // Data capture alignment (quarter-rate selection)
  assert property (snext && (extract_quater.spixel_lsb == C_COL_ODD) && (extract_quater.sline_lsb == C_ROW_ODD) |=> m_axis_tdata == $past(s_axis_tdata));

  // Valid generation alignment (quarter-rate)
  assert property (snext && (extract_quater.spixel_lsb == 1) && (extract_quater.sline_lsb == C_ROW_ODD) |=> m_axis_tvalid);

  // Last propagation when valid is generated
  assert property (snext && (extract_quater.spixel_lsb == 1) && (extract_quater.sline_lsb == C_ROW_ODD) |=> m_axis_tlast == $past(s_axis_tlast));

  // User propagation: set on accepted SOF, held until first mnext, then cleared
  assert property (snext && s_axis_tuser |=> m_axis_tuser until_with mnext);
  assert property (mnext && $past(m_axis_tuser) |=> !m_axis_tuser);

  // Reset effects on internal state and outputs
  assert property (!resetn |=> !m_axis_tvalid && !m_axis_tuser && !m_axis_tlast);
  assert property (!resetn |=> extract_quater.spixel_lsb==0 && extract_quater.sline_lsb==0);

  // Coverage
  cover property (snext && (extract_quater.spixel_lsb == C_COL_ODD) && (extract_quater.sline_lsb == C_ROW_ODD));
  cover property (snext && s_axis_tuser ##[1:$] mnext && m_axis_tuser);
  cover property (m_axis_tvalid && !m_axis_tready ##[2:$] m_axis_tready);
  cover property (snext && s_axis_tlast ##[1:$] snext && s_axis_tlast);
end
endgenerate
`endif
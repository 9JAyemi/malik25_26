// SVA for crossbar_3x2
// Bind this checker to the DUT. Focuses on equivalence to RTL, state updates, and basic sanity.

module crossbar_3x2_sva (
  input logic         aclk,
  input logic         aresetn,

  input  logic [31:0] s_axis_0_tdata,
  input  logic [31:0] s_axis_1_tdata,
  input  logic [31:0] s_axis_2_tdata,
  input  logic        s_axis_0_tvalid,
  input  logic        s_axis_1_tvalid,
  input  logic        s_axis_2_tvalid,
  input  logic        s_axis_0_tready,
  input  logic        s_axis_1_tready,
  input  logic        s_axis_2_tready,

  input  logic [31:0] m_axis_0_tdata,
  input  logic [31:0] m_axis_1_tdata,
  input  logic        m_axis_0_tvalid,
  input  logic        m_axis_1_tvalid,
  input  logic        m_axis_0_tready,
  input  logic        m_axis_1_tready,

  input  logic [1:0]  current_route,
  input  logic [1:0]  next_route
);

  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn)

  // Helpers
  logic any_s_valid;
  assign any_s_valid = s_axis_0_tvalid || s_axis_1_tvalid || s_axis_2_tvalid;

  // Reset behavior
  assert property (!aresetn |-> (current_route==2'd0 && next_route==2'd0));

  // Sanity/X checks
  assert property (!$isunknown({m_axis_0_tvalid,m_axis_1_tvalid,
                                s_axis_0_tready,s_axis_1_tready,s_axis_2_tready,
                                current_route,next_route})));

  // Encoding constraints
  assert property (current_route inside {2'd0,2'd1,2'd2});
  assert property (next_route    inside {2'd0,2'd1,2'd2});

  // TREADY/TVALID definitions (must match RTL)
  assert property (s_axis_0_tready == !(m_axis_0_tvalid || m_axis_1_tvalid));
  assert property (s_axis_1_tready == !(m_axis_0_tvalid || m_axis_1_tvalid));
  assert property (s_axis_2_tready == !m_axis_0_tvalid);
  assert property (m_axis_0_tvalid == (m_axis_0_tready && any_s_valid));
  assert property (m_axis_1_tvalid == (m_axis_1_tready && any_s_valid));
  assert property (s_axis_0_tready == s_axis_1_tready);

  // Data mapping must match route selection
  assert property (m_axis_0_tdata ==
                   (current_route==2'd0 ? s_axis_0_tdata :
                    current_route==2'd1 ? s_axis_1_tdata :
                                           s_axis_2_tdata));
  assert property (m_axis_1_tdata ==
                   (current_route==2'd0 ? s_axis_1_tdata :
                    current_route==2'd1 ? s_axis_2_tdata :
                                           s_axis_0_tdata));

  // next_route update must match RTL (uses $past(next_route) for "hold")
  assert property ((current_route==2'd0) |-> next_route ==
                   ((s_axis_1_tvalid || s_axis_2_tvalid) ? 2'd1 :
                    (s_axis_2_tvalid ? 2'd2 : $past(next_route))));
  assert property ((current_route==2'd1) |-> next_route ==
                   ((s_axis_0_tvalid || s_axis_2_tvalid) ? 2'd0 :
                    (s_axis_2_tvalid ? 2'd2 : $past(next_route))));
  assert property ((current_route==2'd2) |-> next_route ==
                   ((s_axis_0_tvalid || s_axis_1_tvalid) ? 2'd0 :
                    (s_axis_1_tvalid ? 2'd1 : $past(next_route))));

  // current_route update must match RTL "case" on m_axis_*_tvalid (use $past(current_route) for hold)
  assert property ( m_axis_0_tvalid |=> current_route ==
                   ((s_axis_1_tvalid || s_axis_2_tvalid) ? 2'd1 :
                    (s_axis_2_tvalid ? 2'd2 : $past(current_route))));
  assert property ((!m_axis_0_tvalid &&  m_axis_1_tvalid) |=> current_route ==
                   ((s_axis_0_tvalid || s_axis_2_tvalid) ? 2'd0 :
                    (s_axis_2_tvalid ? 2'd2 : $past(current_route))));
  assert property ((!m_axis_0_tvalid && !m_axis_1_tvalid) |=> current_route ==
                   ((s_axis_0_tvalid || s_axis_1_tvalid) ? 2'd0 :
                    (s_axis_1_tvalid ? 2'd1 : $past(current_route))));

  // Coverage
  cover property (current_route==2'd0);
  cover property (current_route==2'd1);
  cover property (current_route==2'd2);

  cover property (m_axis_0_tvalid && m_axis_0_tready);
  cover property (m_axis_1_tvalid && m_axis_1_tready);
  cover property (m_axis_0_tvalid && m_axis_1_tvalid);

  cover property (current_route==2'd0 ##1 current_route==2'd1);
  cover property (current_route==2'd1 ##1 current_route==2'd0);
  cover property (current_route==2'd2 ##1 current_route==2'd0);
  cover property (current_route==2'd0 ##1 current_route==2'd2);
  cover property (current_route==2'd1 ##1 current_route==2'd2);

endmodule

// Bind into DUT
bind crossbar_3x2 crossbar_3x2_sva i_crossbar_3x2_sva (
  .aclk               (aclk),
  .aresetn            (aresetn),
  .s_axis_0_tdata     (s_axis_0_tdata),
  .s_axis_1_tdata     (s_axis_1_tdata),
  .s_axis_2_tdata     (s_axis_2_tdata),
  .s_axis_0_tvalid    (s_axis_0_tvalid),
  .s_axis_1_tvalid    (s_axis_1_tvalid),
  .s_axis_2_tvalid    (s_axis_2_tvalid),
  .s_axis_0_tready    (s_axis_0_tready),
  .s_axis_1_tready    (s_axis_1_tready),
  .s_axis_2_tready    (s_axis_2_tready),
  .m_axis_0_tdata     (m_axis_0_tdata),
  .m_axis_1_tdata     (m_axis_1_tdata),
  .m_axis_0_tvalid    (m_axis_0_tvalid),
  .m_axis_1_tvalid    (m_axis_1_tvalid),
  .m_axis_0_tready    (m_axis_0_tready),
  .m_axis_1_tready    (m_axis_1_tready),
  .current_route      (current_route),
  .next_route         (next_route)
);
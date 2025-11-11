// SVA for spi_engine_interconnect
// Bind-friendly checker that uses DUT internal regs idle and s_active.

module spi_engine_interconnect_sva (
  input  logic        clk,
  input  logic        resetn,

  // DUT ports
  input  logic        m_cmd_ready,
  input  logic        m_sdo_ready,
  input  logic        m_sdi_valid,
  input  logic [7:0]  m_sdi_data,
  input  logic        m_sync_valid,
  input  logic [7:0]  m_sync,

  input  logic        s0_cmd_valid,
  input  logic [15:0] s0_cmd_data,
  input  logic        s0_sdo_valid,
  input  logic [7:0]  s0_sdo_data,
  input  logic        s0_sdi_ready,
  input  logic        s0_sync_ready,

  input  logic        s1_cmd_valid,
  input  logic [15:0] s1_cmd_data,
  input  logic        s1_sdo_valid,
  input  logic [7:0]  s1_sdo_data,
  input  logic        s1_sdi_ready,
  input  logic        s1_sync_ready,

  output logic        m_cmd_valid,
  output logic [15:0] m_cmd_data,
  output logic        m_sdo_valid,
  output logic [7:0]  m_sdo_data,
  output logic        m_sdi_ready,
  output logic        m_sync_ready,
  output logic        s0_cmd_ready,
  output logic        s0_sdo_ready,
  output logic        s0_sdi_valid,
  output logic [7:0]  s0_sdi_data,
  output logic        s0_sync_valid,
  output logic [7:0]  s0_sync,
  output logic        s1_cmd_ready,
  output logic        s1_sdo_ready,
  output logic        s1_sdi_valid,
  output logic [7:0]  s1_sdi_data,
  output logic        s1_sync_valid,
  output logic [7:0]  s1_sync,

  // DUT internals
  input  logic        idle,
  input  logic        s_active
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn)

  // Convenience selects
  wire sel_s0 = (!idle) && (s_active == 1'b0);
  wire sel_s1 = (!idle) && (s_active == 1'b1);

  // Data-path equivalence
  assert property (m_cmd_data == (s_active ? s1_cmd_data : s0_cmd_data));
  assert property (m_sdo_data == (s_active ? s1_sdo_data : s0_sdo_data));
  assert property (s0_sdi_data == m_sdi_data);
  assert property (s1_sdi_data == m_sdi_data);
  assert property (s0_sync    == m_sync);
  assert property (s1_sync    == m_sync);

  // Valid/ready muxing equivalence (concise and complete)
  // cmd
  assert property (m_cmd_valid  == ((!idle) && (s_active ? s1_cmd_valid : s0_cmd_valid)));
  assert property (s0_cmd_ready == (sel_s0 ? m_cmd_ready : 1'b0));
  assert property (s1_cmd_ready == (sel_s1 ? m_cmd_ready : 1'b0));

  // sdo
  assert property (m_sdo_valid  == ((!idle) && (s_active ? s1_sdo_valid : s0_sdo_valid)));
  assert property (s0_sdo_ready == (sel_s0 ? m_sdo_ready : 1'b0));
  assert property (s1_sdo_ready == (sel_s1 ? m_sdo_ready : 1'b0));

  // sdi
  assert property (m_sdi_ready  == ((!idle) && (s_active ? s1_sdi_ready : s0_sdi_ready)));
  assert property (s0_sdi_valid == (sel_s0 ? m_sdi_valid : 1'b0));
  assert property (s1_sdi_valid == (sel_s1 ? m_sdi_valid : 1'b0));

  // sync
  assert property (m_sync_ready  == ((!idle) && (s_active ? s1_sync_ready : s0_sync_ready)));
  assert property (s0_sync_valid == (sel_s0 ? m_sync_valid : 1'b0));
  assert property (s1_sync_valid == (sel_s1 ? m_sync_valid : 1'b0));

  // Idle gating (no activity leaks when idle)
  assert property (idle |-> !m_cmd_valid && !m_sdo_valid &&
                           !s0_cmd_ready && !s1_cmd_ready &&
                           !s0_sdo_ready && !s1_sdo_ready &&
                           !s0_sdi_valid && !s1_sdi_valid &&
                           !m_sdi_ready  &&
                           !s0_sync_valid && !s1_sync_valid &&
                           !m_sync_ready);

  // Mutual exclusion on slave-facing strobes
  assert property (!(s0_cmd_ready && s1_cmd_ready));
  assert property (!(s0_sdo_ready && s1_sdo_ready));
  assert property (!(s0_sdi_valid && s1_sdi_valid));
  assert property (!(s0_sync_valid && s1_sync_valid));

  // s_active stability when active; only changes from idle
  assert property ((!idle && $past(!idle)) |-> $stable(s_active));
  assert property ($changed(s_active) |-> $past(idle));

  // Idle transition causes
  assert property ($fell(idle) |-> $past(s0_cmd_valid || s1_cmd_valid));
  assert property ($rose(idle) |-> $past(m_sync_valid && m_sync_ready));

  // Priority on simultaneous requests when idle
  assert property ($past(idle && s0_cmd_valid && s1_cmd_valid) |-> (s_active == 1'b0));
  assert property ($past(idle && s0_cmd_valid && !s1_cmd_valid) |-> (s_active == 1'b0));
  assert property ($past(idle && !s0_cmd_valid && s1_cmd_valid) |-> (s_active == 1'b1));

  // Handshake equivalence while selected (sanity)
  assert property (sel_s0 |-> ((m_cmd_valid && m_cmd_ready) == (s0_cmd_valid && s0_cmd_ready)));
  assert property (sel_s1 |-> ((m_cmd_valid && m_cmd_ready) == (s1_cmd_valid && s1_cmd_ready)));
  assert property (sel_s0 |-> ((m_sdo_valid && m_sdo_ready) == (s0_sdo_valid && s0_sdo_ready)));
  assert property (sel_s1 |-> ((m_sdo_valid && m_sdo_ready) == (s1_sdo_valid && s1_sdo_ready)));
  assert property (sel_s0 |-> ((m_sdi_valid && m_sdi_ready) == (s0_sdi_valid && s0_sdi_ready)));
  assert property (sel_s1 |-> ((m_sdi_valid && m_sdi_ready) == (s1_sdi_valid && s1_sdi_ready)));
  assert property (sel_s0 |-> ((m_sync_valid && m_sync_ready) == (s0_sync_valid && s0_sync_ready)));
  assert property (sel_s1 |-> ((m_sync_valid && m_sync_ready) == (s1_sync_valid && s1_sync_ready)));

  // Coverage
  cover property (idle ##1 (s0_cmd_valid || s1_cmd_valid) ##1 !idle);
  cover property (idle && s0_cmd_valid && s1_cmd_valid ##1 (s_active==0));
  cover property (sel_s0 && (m_cmd_valid && m_cmd_ready));
  cover property (sel_s1 && (m_cmd_valid && m_cmd_ready));
  cover property (sel_s0 && (m_sdo_valid && m_sdo_ready));
  cover property (sel_s1 && (m_sdo_valid && m_sdo_ready));
  cover property (sel_s0 && (m_sdi_valid && m_sdi_ready));
  cover property (sel_s1 && (m_sdi_valid && m_sdi_ready));
  cover property (!idle && (m_sync_valid && m_sync_ready) ##1 idle);

endmodule

// Bind to all instances of spi_engine_interconnect
bind spi_engine_interconnect spi_engine_interconnect_sva sva_i (
  .clk(clk),
  .resetn(resetn),

  .m_cmd_ready(m_cmd_ready),
  .m_sdo_ready(m_sdo_ready),
  .m_sdi_valid(m_sdi_valid),
  .m_sdi_data(m_sdi_data),
  .m_sync_valid(m_sync_valid),
  .m_sync(m_sync),

  .s0_cmd_valid(s0_cmd_valid),
  .s0_cmd_data(s0_cmd_data),
  .s0_sdo_valid(s0_sdo_valid),
  .s0_sdo_data(s0_sdo_data),
  .s0_sdi_ready(s0_sdi_ready),
  .s0_sync_ready(s0_sync_ready),

  .s1_cmd_valid(s1_cmd_valid),
  .s1_cmd_data(s1_cmd_data),
  .s1_sdo_valid(s1_sdo_valid),
  .s1_sdo_data(s1_sdo_data),
  .s1_sdi_ready(s1_sdi_ready),
  .s1_sync_ready(s1_sync_ready),

  .m_cmd_valid(m_cmd_valid),
  .m_cmd_data(m_cmd_data),
  .m_sdo_valid(m_sdo_valid),
  .m_sdo_data(m_sdo_data),
  .m_sdi_ready(m_sdi_ready),
  .m_sync_ready(m_sync_ready),
  .s0_cmd_ready(s0_cmd_ready),
  .s0_sdo_ready(s0_sdo_ready),
  .s0_sdi_valid(s0_sdi_valid),
  .s0_sdi_data(s0_sdi_data),
  .s0_sync_valid(s0_sync_valid),
  .s0_sync(s0_sync),
  .s1_cmd_ready(s1_cmd_ready),
  .s1_sdo_ready(s1_sdo_ready),
  .s1_sdi_valid(s1_sdi_valid),
  .s1_sdi_data(s1_sdi_data),
  .s1_sync_valid(s1_sync_valid),
  .s1_sync(s1_sync),

  .idle(idle),
  .s_active(s_active)
);
// SVA for VerilogModule
module VerilogModule_sva
(
  input  logic        aclk,
  input  logic        s_dclk_o,
  input  logic [0:0]  Q,
  input  logic        m_axi_wready,
  input  logic [8:0]  burst_count_reg,
  input  logic        tx_fifo_wr,
  input  logic        tx_fifowren_reg,
  input  logic [31:0] tx_fifo_dataout_reg,
  input  logic [0:0]  out,
  input  logic [7:0]  count_d1_reg,
  input  logic [31:0] m_axi_wdata
);

  default clocking cb @(posedge aclk); endclocking

  // Constant outputs must remain 0 (also catches X/Z via ===)
  assert property (out === 1'b0);
  assert property (count_d1_reg === 8'h00);

  // On ready, data must update on the next cycle to the previously presented FIFO data
  assert property (m_axi_wready |=> m_axi_wdata === $past(tx_fifo_dataout_reg));

  // When not ready, data must hold its previous value
  assert property (!m_axi_wready |=> m_axi_wdata === $past(m_axi_wdata));

  // Any change in m_axi_wdata must be caused by a ready in the previous cycle
  assert property ($changed(m_axi_wdata) |-> $past(m_axi_wready));

  // Coverage
  // 1) Observe at least one write update
  cover property (m_axi_wready ##1 (m_axi_wdata === $past(tx_fifo_dataout_reg)));
  // 2) Observe holds over multiple cycles without ready
  cover property (!m_axi_wready [*3] ##1 (m_axi_wdata === $past(m_axi_wdata)));
  // 3) Observe back-to-back updates with data changing
  cover property (m_axi_wready ##1 (m_axi_wready && $changed(m_axi_wdata)));

endmodule

bind VerilogModule VerilogModule_sva sva_VerilogModule (.*);
// SVA for VerilogModule
module VerilogModule_sva
(
  input logic        aclk,
  input logic        m_axi_wready,
  input logic [31:0] tx_fifo_dataout_reg,
  input logic [31:0] m_axi_wdata,
  input logic [7:0]  count_d1_reg,
  input logic [0:0]  out
);

  default clocking cb @(posedge aclk); endclocking
  default disable iff ($isunknown({m_axi_wready, tx_fifo_dataout_reg, m_axi_wdata, count_d1_reg, out}));

  // Constant outputs
  assert property (out == 1'b0);
  assert property (count_d1_reg == 8'h00);

  // Write/update behavior
  assert property ( (m_axi_wready && !$isunknown(tx_fifo_dataout_reg)) |=> (m_axi_wdata == $past(tx_fifo_dataout_reg)) );
  assert property ( (!m_axi_wready && !$isunknown(m_axi_wdata))       |=> (m_axi_wdata == $past(m_axi_wdata)) );

  // Changes on m_axi_wdata must be due to prior write-ready
  assert property ( $changed(m_axi_wdata) |-> $past(m_axi_wready) );

  // Coverage
  cover property (m_axi_wready ##1 $changed(m_axi_wdata));                  // at least one write causes an update
  cover property (!m_axi_wready [*3] ##1 !$changed(m_axi_wdata));           // idle stretch holds data
  cover property (m_axi_wready ##1 m_axi_wready ##1 m_axi_wready);          // back-to-back writes

endmodule

bind VerilogModule VerilogModule_sva sva_inst (.*);
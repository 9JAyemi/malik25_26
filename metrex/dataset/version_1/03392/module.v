
module VerilogModule
   (out,
    count_d1_reg,
    m_axi_wdata,
    aclk,
    s_dclk_o,
    Q,
    m_axi_wready,
    burst_count_reg,
    tx_fifo_wr,
    tx_fifowren_reg,
    tx_fifo_dataout_reg);
  output [0:0]out;
  output [7:0]count_d1_reg;
  output [31:0]m_axi_wdata;
  input aclk;
  input s_dclk_o;
  input [0:0]Q;
  input m_axi_wready;
  input [8:0]burst_count_reg;
  input tx_fifo_wr;
  input tx_fifowren_reg;
  input [31:0]tx_fifo_dataout_reg;

  reg [31:0]m_axi_wdata_reg;

  assign out = 1'b0;

  always @(posedge aclk) begin
    if (m_axi_wready) begin
      m_axi_wdata_reg <= tx_fifo_dataout_reg;
    end
  end

  assign m_axi_wdata = m_axi_wdata_reg;

  assign count_d1_reg = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0};

endmodule
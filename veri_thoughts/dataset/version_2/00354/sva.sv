module VerilogModule_sva (
    input logic [0:0] out,
    input logic [7:0] count_d1_reg,
    input logic [31:0] m_axi_wdata,
    input logic aclk,
    input logic s_dclk_o,
    input logic [0:0] Q,
    input logic m_axi_wready,
    input logic [8:0] burst_count_reg,
    input logic tx_fifo_wr,
    input logic tx_fifowren_reg,
    input logic [31:0] tx_fifo_dataout_reg
);

    // out is permanently tied low.
    check_out_tied_low: assert property (
        @(posedge aclk) out == 1'b0
    );

    // count_d1_reg is permanently zero.
    check_count_d1_reg_zero: assert property (
        @(posedge aclk) count_d1_reg == 8'h00
    );

    // A ready cycle loads tx_fifo_dataout_reg into m_axi_wdata by the next clock.
    check_wdata_captures_tx_fifo_on_ready: assert property (
        @(posedge aclk) m_axi_wready |=> (m_axi_wdata == $past(tx_fifo_dataout_reg))
    );

    // Without ready, m_axi_wdata holds its previous value.
    check_wdata_holds_when_not_ready: assert property (
        @(posedge aclk) !m_axi_wready |=> (m_axi_wdata == $past(m_axi_wdata))
    );

endmodule
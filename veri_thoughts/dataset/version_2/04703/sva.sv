module membus_3_connect_sva(
    input logic clk,
    input logic reset,

    input logic m_wr_rs,
    input logic m_rq_cyc,
    input logic m_rd_rq,
    input logic m_wr_rq,
    input logic [21:35] m_ma,
    input logic [18:21] m_sel,
    input logic m_fmc_select,
    input logic [0:35] m_mb_write,
    input logic m_addr_ack,
    input logic m_rd_rs,
    input logic [0:35] m_mb_read,

    input logic s0_wr_rs,
    input logic s0_rq_cyc,
    input logic s0_rd_rq,
    input logic s0_wr_rq,
    input logic [21:35] s0_ma,
    input logic [18:21] s0_sel,
    input logic s0_fmc_select,
    input logic [0:35] s0_mb_write,
    input logic s0_addr_ack,
    input logic s0_rd_rs,
    input logic [0:35] s0_mb_read,

    input logic s1_wr_rs,
    input logic s1_rq_cyc,
    input logic s1_rd_rq,
    input logic s1_wr_rq,
    input logic [21:35] s1_ma,
    input logic [18:21] s1_sel,
    input logic s1_fmc_select,
    input logic [0:35] s1_mb_write,
    input logic s1_addr_ack,
    input logic s1_rd_rs,
    input logic [0:35] s1_mb_read,

    input logic s2_wr_rs,
    input logic s2_rq_cyc,
    input logic s2_rd_rq,
    input logic s2_wr_rq,
    input logic [21:35] s2_ma,
    input logic [18:21] s2_sel,
    input logic s2_fmc_select,
    input logic [0:35] s2_mb_write,
    input logic s2_addr_ack,
    input logic s2_rd_rs,
    input logic [0:35] s2_mb_read
);

    // Master address acknowledge is the OR of all slave acknowledges.
    check_master_addr_ack_or: assert property (
        @(posedge clk) disable iff (reset)
        m_addr_ack == (s0_addr_ack | s1_addr_ack | s2_addr_ack)
    );

    // Master read response is the OR of all slave read responses.
    check_master_rd_rs_or: assert property (
        @(posedge clk) disable iff (reset)
        m_rd_rs == (s0_rd_rs | s1_rd_rs | s2_rd_rs)
    );

    // Master read data is the OR of write data and all slave read data.
    check_master_read_data_or: assert property (
        @(posedge clk) disable iff (reset)
        m_mb_read == (m_mb_write | s0_mb_read | s1_mb_read | s2_mb_read)
    );

    // Slave 0 request and address signals mirror the master inputs.
    check_s0_request_fanout: assert property (
        @(posedge clk) disable iff (reset)
        (s0_wr_rs == m_wr_rs) &&
        (s0_rq_cyc == m_rq_cyc) &&
        (s0_rd_rq == m_rd_rq) &&
        (s0_wr_rq == m_wr_rq) &&
        (s0_ma == m_ma) &&
        (s0_sel == m_sel) &&
        (s0_fmc_select == m_fmc_select)
    );

    // Slave 0 write data matches the shared ORed data bus.
    check_s0_write_data_fanout: assert property (
        @(posedge clk) disable iff (reset)
        s0_mb_write == (m_mb_write | s0_mb_read | s1_mb_read | s2_mb_read)
    );

    // Slave 1 request and address signals mirror the master inputs.
    check_s1_request_fanout: assert property (
        @(posedge clk) disable iff (reset)
        (s1_wr_rs == m_wr_rs) &&
        (s1_rq_cyc == m_rq_cyc) &&
        (s1_rd_rq == m_rd_rq) &&
        (s1_wr_rq == m_wr_rq) &&
        (s1_ma == m_ma) &&
        (s1_sel == m_sel) &&
        (s1_fmc_select == m_fmc_select)
    );

    // Slave 1 write data matches the shared ORed data bus.
    check_s1_write_data_fanout: assert property (
        @(posedge clk) disable iff (reset)
        s1_mb_write == (m_mb_write | s0_mb_read | s1_mb_read | s2_mb_read)
    );

    // Slave 2 request and address signals mirror the master inputs.
    check_s2_request_fanout: assert property (
        @(posedge clk) disable iff (reset)
        (s2_wr_rs == m_wr_rs) &&
        (s2_rq_cyc == m_rq_cyc) &&
        (s2_rd_rq == m_rd_rq) &&
        (s2_wr_rq == m_wr_rq) &&
        (s2_ma == m_ma) &&
        (s2_sel == m_sel) &&
        (s2_fmc_select == m_fmc_select)
    );

    // Slave 2 write data matches the shared ORed data bus.
    check_s2_write_data_fanout: assert property (
        @(posedge clk) disable iff (reset)
        s2_mb_write == (m_mb_write | s0_mb_read | s1_mb_read | s2_mb_read)
    );

endmodule
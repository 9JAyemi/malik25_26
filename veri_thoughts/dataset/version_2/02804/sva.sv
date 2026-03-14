module membus_2_connect_sva (
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
    input logic [0:35] s1_mb_read
);
    ///// OR-combine returns to master /////
    // m_addr_ack is the OR of s0_addr_ack and s1_addr_ack.
    check_m_addr_ack_or: assert property (
        @(posedge clk) disable iff (reset) m_addr_ack == (s0_addr_ack | s1_addr_ack)
    );
    // m_rd_rs is the OR of s0_rd_rs and s1_rd_rs.
    check_m_rd_rs_or: assert property (
        @(posedge clk) disable iff (reset) m_rd_rs == (s0_rd_rs | s1_rd_rs)
    );

    ///// Shared ORed data bus /////
    // m_mb_read equals m_mb_write | s0_mb_read | s1_mb_read.
    check_m_mb_read_or: assert property (
        @(posedge clk) disable iff (reset) m_mb_read == (m_mb_write | s0_mb_read | s1_mb_read)
    );
    // s0_mb_write equals m_mb_write | s0_mb_read | s1_mb_read.
    check_s0_mb_write_or: assert property (
        @(posedge clk) disable iff (reset) s0_mb_write == (m_mb_write | s0_mb_read | s1_mb_read)
    );
    // s1_mb_write equals m_mb_write | s0_mb_read | s1_mb_read.
    check_s1_mb_write_or: assert property (
        @(posedge clk) disable iff (reset) s1_mb_write == (m_mb_write | s0_mb_read | s1_mb_read)
    );
    // The ORed bus value is consistent across m_mb_read and s0_mb_write.
    check_mb_bus_consistency_s0: assert property (
        @(posedge clk) disable iff (reset) s0_mb_write == m_mb_read
    );
    // The ORed bus value is consistent across m_mb_read and s1_mb_write.
    check_mb_bus_consistency_s1: assert property (
        @(posedge clk) disable iff (reset) s1_mb_write == m_mb_read
    );

    ///// Pass-through of master control/address to both slaves /////
    // s0_wr_rs passes through m_wr_rs.
    pass_s0_wr_rs: assert property (
        @(posedge clk) disable iff (reset) s0_wr_rs == m_wr_rs
    );
    // s1_wr_rs passes through m_wr_rs.
    pass_s1_wr_rs: assert property (
        @(posedge clk) disable iff (reset) s1_wr_rs == m_wr_rs
    );
    // s0_rq_cyc passes through m_rq_cyc.
    pass_s0_rq_cyc: assert property (
        @(posedge clk) disable iff (reset) s0_rq_cyc == m_rq_cyc
    );
    // s1_rq_cyc passes through m_rq_cyc.
    pass_s1_rq_cyc: assert property (
        @(posedge clk) disable iff (reset) s1_rq_cyc == m_rq_cyc
    );
    // s0_rd_rq passes through m_rd_rq.
    pass_s0_rd_rq: assert property (
        @(posedge clk) disable iff (reset) s0_rd_rq == m_rd_rq
    );
    // s1_rd_rq passes through m_rd_rq.
    pass_s1_rd_rq: assert property (
        @(posedge clk) disable iff (reset) s1_rd_rq == m_rd_rq
    );
    // s0_wr_rq passes through m_wr_rq.
    pass_s0_wr_rq: assert property (
        @(posedge clk) disable iff (reset) s0_wr_rq == m_wr_rq
    );
    // s1_wr_rq passes through m_wr_rq.
    pass_s1_wr_rq: assert property (
        @(posedge clk) disable iff (reset) s1_wr_rq == m_wr_rq
    );
    // s0_ma passes through m_ma.
    pass_s0_ma: assert property (
        @(posedge clk) disable iff (reset) s0_ma == m_ma
    );
    // s1_ma passes through m_ma.
    pass_s1_ma: assert property (
        @(posedge clk) disable iff (reset) s1_ma == m_ma
    );
    // s0_sel passes through m_sel.
    pass_s0_sel: assert property (
        @(posedge clk) disable iff (reset) s0_sel == m_sel
    );
    // s1_sel passes through m_sel.
    pass_s1_sel: assert property (
        @(posedge clk) disable iff (reset) s1_sel == m_sel
    );
    // s0_fmc_select passes through m_fmc_select.
    pass_s0_fmc_select: assert property (
        @(posedge clk) disable iff (reset) s0_fmc_select == m_fmc_select
    );
    // s1_fmc_select passes through m_fmc_select.
    pass_s1_fmc_select: assert property (
        @(posedge clk) disable iff (reset) s1_fmc_select == m_fmc_select
    );
endmodule
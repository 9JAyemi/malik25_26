module iobus_3_connect_sva(
    input logic clk,
    input logic reset,

    input logic m_iob_poweron,
    input logic m_iob_reset,
    input logic m_datao_clear,
    input logic m_datao_set,
    input logic m_cono_clear,
    input logic m_cono_set,
    input logic m_iob_fm_datai,
    input logic m_iob_fm_status,
    input logic m_rdi_pulse,
    input logic [3:9] m_ios,
    input logic [0:35] m_iob_write,
    input logic [1:7] m_pi_req,
    input logic [0:35] m_iob_read,
    input logic m_dr_split,
    input logic m_rdi_data,

    input logic s0_iob_poweron,
    input logic s0_iob_reset,
    input logic s0_datao_clear,
    input logic s0_datao_set,
    input logic s0_cono_clear,
    input logic s0_cono_set,
    input logic s0_iob_fm_datai,
    input logic s0_iob_fm_status,
    input logic s0_rdi_pulse,
    input logic [3:9] s0_ios,
    input logic [0:35] s0_iob_write,
    input logic [1:7] s0_pi_req,
    input logic [0:35] s0_iob_read,
    input logic s0_dr_split,
    input logic s0_rdi_data,

    input logic s1_iob_poweron,
    input logic s1_iob_reset,
    input logic s1_datao_clear,
    input logic s1_datao_set,
    input logic s1_cono_clear,
    input logic s1_cono_set,
    input logic s1_iob_fm_datai,
    input logic s1_iob_fm_status,
    input logic s1_rdi_pulse,
    input logic [3:9] s1_ios,
    input logic [0:35] s1_iob_write,
    input logic [1:7] s1_pi_req,
    input logic [0:35] s1_iob_read,
    input logic s1_dr_split,
    input logic s1_rdi_data,

    input logic s2_iob_poweron,
    input logic s2_iob_reset,
    input logic s2_datao_clear,
    input logic s2_datao_set,
    input logic s2_cono_clear,
    input logic s2_cono_set,
    input logic s2_iob_fm_datai,
    input logic s2_iob_fm_status,
    input logic s2_rdi_pulse,
    input logic [3:9] s2_ios,
    input logic [0:35] s2_iob_write,
    input logic [1:7] s2_pi_req,
    input logic [0:35] s2_iob_read,
    input logic s2_dr_split,
    input logic s2_rdi_data
);
    ///// OR-combine outputs toward master /////
    // m_pi_req is bitwise OR of all slave pi_req.
    check_m_pi_req_or: assert property (
        @(posedge clk) disable iff (reset) m_pi_req == (s0_pi_req | s1_pi_req | s2_pi_req)
    );
    // m_iob_read is bitwise OR of master write and all slave read.
    check_m_iob_read_or: assert property (
        @(posedge clk) disable iff (reset) m_iob_read == (m_iob_write | s0_iob_read | s1_iob_read | s2_iob_read)
    );
    // m_dr_split is OR of all slave dr_split.
    check_m_dr_split_or: assert property (
        @(posedge clk) disable iff (reset) m_dr_split == (s0_dr_split | s1_dr_split | s2_dr_split)
    );
    // m_rdi_data is OR of all slave rdi_data.
    check_m_rdi_data_or: assert property (
        @(posedge clk) disable iff (reset) m_rdi_data == (s0_rdi_data | s1_rdi_data | s2_rdi_data)
    );

    ///// Pass-through from master to slave 0 /////
    // All 1-bit control/status signals pass through to s0.
    check_s0_ctrl_passthrough: assert property (
        @(posedge clk) disable iff (reset)
            {s0_iob_poweron, s0_iob_reset, s0_datao_clear, s0_datao_set, s0_cono_clear, s0_cono_set,
             s0_iob_fm_datai, s0_iob_fm_status, s0_rdi_pulse}
          =={m_iob_poweron, m_iob_reset, m_datao_clear, m_datao_set, m_cono_clear, m_cono_set,
             m_iob_fm_datai, m_iob_fm_status, m_rdi_pulse}
    );
    // IOS bus passes through to s0.
    check_s0_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_ios == m_ios
    );
    // IOB write bus passes through to s0.
    check_s0_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_iob_write == m_iob_write
    );

    ///// Pass-through from master to slave 1 /////
    // All 1-bit control/status signals pass through to s1.
    check_s1_ctrl_passthrough: assert property (
        @(posedge clk) disable iff (reset)
            {s1_iob_poweron, s1_iob_reset, s1_datao_clear, s1_datao_set, s1_cono_clear, s1_cono_set,
             s1_iob_fm_datai, s1_iob_fm_status, s1_rdi_pulse}
          =={m_iob_poweron, m_iob_reset, m_datao_clear, m_datao_set, m_cono_clear, m_cono_set,
             m_iob_fm_datai, m_iob_fm_status, m_rdi_pulse}
    );
    // IOS bus passes through to s1.
    check_s1_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_ios == m_ios
    );
    // IOB write bus passes through to s1.
    check_s1_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_iob_write == m_iob_write
    );

    ///// Pass-through from master to slave 2 /////
    // All 1-bit control/status signals pass through to s2.
    check_s2_ctrl_passthrough: assert property (
        @(posedge clk) disable iff (reset)
            {s2_iob_poweron, s2_iob_reset, s2_datao_clear, s2_datao_set, s2_cono_clear, s2_cono_set,
             s2_iob_fm_datai, s2_iob_fm_status, s2_rdi_pulse}
          =={m_iob_poweron, m_iob_reset, m_datao_clear, m_datao_set, m_cono_clear, m_cono_set,
             m_iob_fm_datai, m_iob_fm_status, m_rdi_pulse}
    );
    // IOS bus passes through to s2.
    check_s2_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_ios == m_ios
    );
    // IOB write bus passes through to s2.
    check_s2_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_iob_write == m_iob_write
    );
endmodule
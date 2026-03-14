module iobus_4_connect_sva (
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
    input logic s2_rdi_data,

    input logic s3_iob_poweron,
    input logic s3_iob_reset,
    input logic s3_datao_clear,
    input logic s3_datao_set,
    input logic s3_cono_clear,
    input logic s3_cono_set,
    input logic s3_iob_fm_datai,
    input logic s3_iob_fm_status,
    input logic s3_rdi_pulse,
    input logic [3:9] s3_ios,
    input logic [0:35] s3_iob_write,
    input logic [1:7] s3_pi_req,
    input logic [0:35] s3_iob_read,
    input logic s3_dr_split,
    input logic s3_rdi_data
);
    ///// Aggregation (OR) outputs /////
    // m_pi_req is the bitwise OR of all slave s*_pi_req.
    check_m_pi_req_or: assert property (
        @(posedge clk) disable iff (reset) m_pi_req == (s0_pi_req | s1_pi_req | s2_pi_req | s3_pi_req)
    );
    // m_iob_read is the bitwise OR of m_iob_write and all slave s*_iob_read.
    check_m_iob_read_or: assert property (
        @(posedge clk) disable iff (reset) m_iob_read == (m_iob_write | s0_iob_read | s1_iob_read | s2_iob_read | s3_iob_read)
    );
    // m_dr_split is the OR of all slave s*_dr_split.
    check_m_dr_split_or: assert property (
        @(posedge clk) disable iff (reset) m_dr_split == (s0_dr_split | s1_dr_split | s2_dr_split | s3_dr_split)
    );
    // m_rdi_data is the OR of all slave s*_rdi_data.
    check_m_rdi_data_or: assert property (
        @(posedge clk) disable iff (reset) m_rdi_data == (s0_rdi_data | s1_rdi_data | s2_rdi_data | s3_rdi_data)
    );

    ///// Broadcast to s0 /////
    // s0_iob_poweron equals m_iob_poweron.
    check_s0_iob_poweron_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_iob_poweron == m_iob_poweron
    );
    // s0_iob_reset equals m_iob_reset.
    check_s0_iob_reset_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_iob_reset == m_iob_reset
    );
    // s0_datao_clear equals m_datao_clear.
    check_s0_datao_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_datao_clear == m_datao_clear
    );
    // s0_datao_set equals m_datao_set.
    check_s0_datao_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_datao_set == m_datao_set
    );
    // s0_cono_clear equals m_cono_clear.
    check_s0_cono_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_cono_clear == m_cono_clear
    );
    // s0_cono_set equals m_cono_set.
    check_s0_cono_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_cono_set == m_cono_set
    );
    // s0_iob_fm_datai equals m_iob_fm_datai.
    check_s0_iob_fm_datai_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_iob_fm_datai == m_iob_fm_datai
    );
    // s0_iob_fm_status equals m_iob_fm_status.
    check_s0_iob_fm_status_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_iob_fm_status == m_iob_fm_status
    );
    // s0_rdi_pulse equals m_rdi_pulse.
    check_s0_rdi_pulse_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_rdi_pulse == m_rdi_pulse
    );
    // s0_ios equals m_ios.
    check_s0_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_ios == m_ios
    );
    // s0_iob_write equals m_iob_write.
    check_s0_iob_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s0_iob_write == m_iob_write
    );

    ///// Broadcast to s1 /////
    // s1_iob_poweron equals m_iob_poweron.
    check_s1_iob_poweron_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_iob_poweron == m_iob_poweron
    );
    // s1_iob_reset equals m_iob_reset.
    check_s1_iob_reset_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_iob_reset == m_iob_reset
    );
    // s1_datao_clear equals m_datao_clear.
    check_s1_datao_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_datao_clear == m_datao_clear
    );
    // s1_datao_set equals m_datao_set.
    check_s1_datao_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_datao_set == m_datao_set
    );
    // s1_cono_clear equals m_cono_clear.
    check_s1_cono_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_cono_clear == m_cono_clear
    );
    // s1_cono_set equals m_cono_set.
    check_s1_cono_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_cono_set == m_cono_set
    );
    // s1_iob_fm_datai equals m_iob_fm_datai.
    check_s1_iob_fm_datai_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_iob_fm_datai == m_iob_fm_datai
    );
    // s1_iob_fm_status equals m_iob_fm_status.
    check_s1_iob_fm_status_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_iob_fm_status == m_iob_fm_status
    );
    // s1_rdi_pulse equals m_rdi_pulse.
    check_s1_rdi_pulse_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_rdi_pulse == m_rdi_pulse
    );
    // s1_ios equals m_ios.
    check_s1_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_ios == m_ios
    );
    // s1_iob_write equals m_iob_write.
    check_s1_iob_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s1_iob_write == m_iob_write
    );

    ///// Broadcast to s2 /////
    // s2_iob_poweron equals m_iob_poweron.
    check_s2_iob_poweron_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_iob_poweron == m_iob_poweron
    );
    // s2_iob_reset equals m_iob_reset.
    check_s2_iob_reset_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_iob_reset == m_iob_reset
    );
    // s2_datao_clear equals m_datao_clear.
    check_s2_datao_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_datao_clear == m_datao_clear
    );
    // s2_datao_set equals m_datao_set.
    check_s2_datao_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_datao_set == m_datao_set
    );
    // s2_cono_clear equals m_cono_clear.
    check_s2_cono_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_cono_clear == m_cono_clear
    );
    // s2_cono_set equals m_cono_set.
    check_s2_cono_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_cono_set == m_cono_set
    );
    // s2_iob_fm_datai equals m_iob_fm_datai.
    check_s2_iob_fm_datai_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_iob_fm_datai == m_iob_fm_datai
    );
    // s2_iob_fm_status equals m_iob_fm_status.
    check_s2_iob_fm_status_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_iob_fm_status == m_iob_fm_status
    );
    // s2_rdi_pulse equals m_rdi_pulse.
    check_s2_rdi_pulse_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_rdi_pulse == m_rdi_pulse
    );
    // s2_ios equals m_ios.
    check_s2_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_ios == m_ios
    );
    // s2_iob_write equals m_iob_write.
    check_s2_iob_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s2_iob_write == m_iob_write
    );

    ///// Broadcast to s3 /////
    // s3_iob_poweron equals m_iob_poweron.
    check_s3_iob_poweron_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_iob_poweron == m_iob_poweron
    );
    // s3_iob_reset equals m_iob_reset.
    check_s3_iob_reset_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_iob_reset == m_iob_reset
    );
    // s3_datao_clear equals m_datao_clear.
    check_s3_datao_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_datao_clear == m_datao_clear
    );
    // s3_datao_set equals m_datao_set.
    check_s3_datao_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_datao_set == m_datao_set
    );
    // s3_cono_clear equals m_cono_clear.
    check_s3_cono_clear_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_cono_clear == m_cono_clear
    );
    // s3_cono_set equals m_cono_set.
    check_s3_cono_set_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_cono_set == m_cono_set
    );
    // s3_iob_fm_datai equals m_iob_fm_datai.
    check_s3_iob_fm_datai_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_iob_fm_datai == m_iob_fm_datai
    );
    // s3_iob_fm_status equals m_iob_fm_status.
    check_s3_iob_fm_status_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_iob_fm_status == m_iob_fm_status
    );
    // s3_rdi_pulse equals m_rdi_pulse.
    check_s3_rdi_pulse_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_rdi_pulse == m_rdi_pulse
    );
    // s3_ios equals m_ios.
    check_s3_ios_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_ios == m_ios
    );
    // s3_iob_write equals m_iob_write.
    check_s3_iob_write_passthrough: assert property (
        @(posedge clk) disable iff (reset) s3_iob_write == m_iob_write
    );
endmodule
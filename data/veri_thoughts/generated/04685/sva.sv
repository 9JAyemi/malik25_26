module system_auto_cc_0_rd_status_flags_as_19_sva (
    input logic       out,
    input logic [1:0] count_d1_reg,
    input logic       m_aclk,
    input logic       rd_rst_reg_reg
);

    // Synchronous reset loads out high on the following clock sample.
    check_reset_loads_out_high: assert property (
        @(posedge m_aclk)
        rd_rst_reg_reg |=> (out == 1'b1)
    );

    // When not in reset, a high count_d1_reg[1] is captured into out.
    check_capture_count_bit_high: assert property (
        @(posedge m_aclk) disable iff (rd_rst_reg_reg)
        (count_d1_reg[1] == 1'b1) |=> (out == 1'b1)
    );

    // When not in reset, a low count_d1_reg[1] is captured into out.
    check_capture_count_bit_low: assert property (
        @(posedge m_aclk) disable iff (rd_rst_reg_reg)
        (count_d1_reg[1] == 1'b0) |=> (out == 1'b0)
    );

    // A rising count_d1_reg[1] propagates to a rising out one cycle later.
    check_rising_count_bit_propagates_to_out: assert property (
        @(posedge m_aclk) disable iff (rd_rst_reg_reg)
        ((count_d1_reg[1] == 1'b0) ##1 (count_d1_reg[1] == 1'b1)) |=> $rose(out)
    );

    // A falling count_d1_reg[1] propagates to a falling out one cycle later.
    check_falling_count_bit_propagates_to_out: assert property (
        @(posedge m_aclk) disable iff (rd_rst_reg_reg)
        ((count_d1_reg[1] == 1'b1) ##1 (count_d1_reg[1] == 1'b0)) |=> $fell(out)
    );

endmodule
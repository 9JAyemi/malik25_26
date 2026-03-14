module system_axi_quad_spi_shield_0_wr_status_flags_as_sva (
    input logic \gic0.gc1.count_reg[0] ,
    input logic [0:0] E,
    input logic \gic0.gc1.count_d2_reg[0] ,
    input logic s_axi_aclk,
    input logic out,
    input logic p_6_in,
    input logic ip2Bus_WrAck_core_reg_1,
    input logic Bus_RNW_reg
);
    // E is tied LOW continuously.
    check_E_constant_low: assert property (
        @(posedge s_axi_aclk) disable iff (1'b0) (E[0] == 1'b0)
    );

    // When Bus_RNW_reg is HIGH, count_reg[0] is forced to 0 four cycles later.
    check_count_zero_4_after_Bus_RNW_high: assert property (
        @(posedge s_axi_aclk) disable iff (1'b0) (Bus_RNW_reg == 1'b1) |-> ##4 (\gic0.gc1.count_reg[0]  == 1'b0)
    );

    // A rising edge on Bus_RNW_reg also clears count_reg[0] after four cycles.
    check_count_zero_4_after_Bus_RNW_rose: assert property (
        @(posedge s_axi_aclk) disable iff (1'b0) $rose(Bus_RNW_reg) |-> ##4 (\gic0.gc1.count_reg[0]  == 1'b0)
    );

    // If Bus_RNW_reg was HIGH 4 cycles ago, count_reg[0] is 0 now.
    check_count_zero_now_if_Bus_RNW_high_4ago: assert property (
        @(posedge s_axi_aclk) disable iff (1'b0) ($past(Bus_RNW_reg,4) == 1'b1) |-> (\gic0.gc1.count_reg[0]  == 1'b0)
    );

    // Two-cycle HIGH on Bus_RNW_reg maps to two-cycle 0 on count four cycles later.
    check_sustained_high_2_maps_to_two_zeros: assert property (
        @(posedge s_axi_aclk) disable iff (1'b0) (Bus_RNW_reg [*2]) |-> ##4 ((\gic0.gc1.count_reg[0]  == 1'b0) [*2])
    );

    // Four-cycle HIGH on Bus_RNW_reg maps to four-cycle 0 on count four cycles later.
    check_sustained_high_4_maps_to_four_zeros: assert property (
        @(posedge s_axi_aclk) disable iff (1'b0) (Bus_RNW_reg [*4]) |-> ##4 ((\gic0.gc1.count_reg[0]  == 1'b0) [*4])
    );
endmodule
module pcie_7x_0_core_top_gtp_cpllpd_ovrd_sva (
    input  logic         i_ibufds_gte2,
    input  logic         o_cpllpd_ovrd,
    input  logic         o_cpllreset_ovrd,
    input  logic [95:0]  cpllpd_wait,
    input  logic [127:0] cpllreset_wait
);
    // Clock: i_ibufds_gte2 (posedge). No reset port in RTL.

    // cpllpd_wait shifts left by 1 and inserts 0 at LSB each clk.
    check_cpllpd_wait_shift: assert property (
        @(posedge i_ibufds_gte2) !$initstate |-> (cpllpd_wait == { $past(cpllpd_wait[94:0]), 1'b0 })
    );

    // cpllreset_wait shifts left by 1 and inserts 0 at LSB each clk.
    check_cpllreset_wait_shift: assert property (
        @(posedge i_ibufds_gte2) !$initstate |-> (cpllreset_wait == { $past(cpllreset_wait[126:0]), 1'b0 })
    );

    // cpllpd_wait MSB equals previous bit[94].
    check_cpllpd_msb_follows_bit94: assert property (
        @(posedge i_ibufds_gte2) !$initstate |-> (cpllpd_wait[95] == $past(cpllpd_wait[94]))
    );

    // cpllreset_wait MSB equals previous bit[126].
    check_cpllreset_msb_follows_bit126: assert property (
        @(posedge i_ibufds_gte2) !$initstate |-> (cpllreset_wait[127] == $past(cpllreset_wait[126]))
    );

    // After the first update, cpllpd_wait LSB is always 0.
    check_cpllpd_lsb_zero: assert property (
        @(posedge i_ibufds_gte2) !$initstate |-> (cpllpd_wait[0] == 1'b0)
    );

    // After the first update, cpllreset_wait LSB is always 0.
    check_cpllreset_lsb_zero: assert property (
        @(posedge i_ibufds_gte2) !$initstate |-> (cpllreset_wait[0] == 1'b0)
    );

    // o_cpllpd_ovrd equals cpllpd_wait MSB.
    map_o_cpllpd_to_msb: assert property (
        @(posedge i_ibufds_gte2) (o_cpllpd_ovrd == cpllpd_wait[95])
    );

    // o_cpllreset_ovrd equals cpllreset_wait MSB.
    map_o_cpllreset_to_msb: assert property (
        @(posedge i_ibufds_gte2) (o_cpllreset_ovrd == cpllreset_wait[127])
    );

    // With zero-fill shifting, cpllpd_wait becomes all-zero 96 cycles later from any time.
    eventually_zero_cpllpd_wait: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##96 (cpllpd_wait == 96'b0)
    );

    // With zero-fill shifting, cpllreset_wait becomes all-zero 128 cycles later from any time.
    eventually_zero_cpllreset_wait: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 (cpllreset_wait == 128'b0)
    );

    // Consequently, o_cpllpd_ovrd is 0 96 cycles later from any time.
    eventually_zero_o_cpllpd: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##96 (o_cpllpd_ovrd == 1'b0)
    );

    // Consequently, o_cpllreset_ovrd is 0 128 cycles later from any time.
    eventually_zero_o_cpllreset: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 (o_cpllreset_ovrd == 1'b0)
    );

    // Initial contents per RTL: cpllpd_wait all 1s; cpllreset_wait has 8 LSB 1s.
    init_shift_regs_correct: assert property (
        @(posedge i_ibufds_gte2) $initstate |-> (cpllpd_wait == 96'hFFFFFFFFFFFFFFFFFFFFFFFF) && (cpllreset_wait == 128'h000000000000000000000000000000FF)
    );

    // Initial output levels per RTL mapping (MSBs of initial registers).
    init_outputs_levels: assert property (
        @(posedge i_ibufds_gte2) $initstate |-> (o_cpllpd_ovrd == 1'b1) && (o_cpllreset_ovrd == 1'b0)
    );

    // From init, o_cpllpd_ovrd stays HIGH for the first 96 cycles.
    init_o_cpllpd_high_96: assert property (
        @(posedge i_ibufds_gte2) $initstate |-> (o_cpllpd_ovrd [*96])
    );

    // From init, o_cpllreset_ovrd stays LOW for the first 120 cycles.
    init_o_cpllreset_low_120: assert property (
        @(posedge i_ibufds_gte2) $initstate |-> (!o_cpllreset_ovrd [*120])
    );

    // From init, o_cpllreset_ovrd is HIGH for 8 cycles starting at cycle 120.
    init_o_cpllreset_high_window: assert property (
        @(posedge i_ibufds_gte2) $initstate |-> ##120 (o_cpllreset_ovrd [*8])
    );
endmodule
module PCIeGen2x8If128_gtp_cpllpd_ovrd_sva (
    input logic i_ibufds_gte2,
    input logic o_cpllpd_ovrd,
    input logic o_cpllreset_ovrd
);
    // After 96 clocks, o_cpllpd_ovrd must be 0.
    cpllpd_zero_after_96: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##96 (o_cpllpd_ovrd == 1'b0)
    );

    // After 128 clocks, o_cpllreset_ovrd must be 0.
    cpllreset_zero_after_128: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 (o_cpllreset_ovrd == 1'b0)
    );

    // After 96 clocks, o_cpllpd_ovrd remains 0 for at least 64 clocks.
    cpllpd_zero_hold_64_post96: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##96 (o_cpllpd_ovrd == 1'b0)[*64]
    );

    // After 128 clocks, o_cpllreset_ovrd remains 0 for at least 64 clocks.
    cpllreset_zero_hold_64_post128: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 (o_cpllreset_ovrd == 1'b0)[*64]
    );

    // Any 96-cycle run of o_cpllpd_ovrd=1 must be followed by 0 on the next cycle.
    cpllpd_ones_run_capped_96: assert property (
        @(posedge i_ibufds_gte2) (o_cpllpd_ovrd == 1'b1)[*96] |-> (o_cpllpd_ovrd == 1'b0)
    );

    // Any 128-cycle run of o_cpllreset_ovrd=1 must be followed by 0 on the next cycle.
    cpllreset_ones_run_capped_128: assert property (
        @(posedge i_ibufds_gte2) (o_cpllreset_ovrd == 1'b1)[*128] |-> (o_cpllreset_ovrd == 1'b0)
    );

    // After 128 clocks, both outputs must be 0 simultaneously.
    both_zero_after_128: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 ((o_cpllpd_ovrd == 1'b0) && (o_cpllreset_ovrd == 1'b0))
    );

    // o_cpllpd_ovrd is known (not X/Z) after 96 clocks.
    cpllpd_known_after_96: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##96 (!$isunknown(o_cpllpd_ovrd))
    );

    // o_cpllreset_ovrd is known (not X/Z) after 128 clocks.
    cpllreset_known_after_128: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 (!$isunknown(o_cpllreset_ovrd))
    );

    // After 128 clocks, both outputs stay 0 for at least 64 clocks.
    both_zero_hold_64_post128: assert property (
        @(posedge i_ibufds_gte2) 1'b1 |-> ##128 ((o_cpllpd_ovrd == 1'b0) && (o_cpllreset_ovrd == 1'b0))[*64]
    );
endmodule
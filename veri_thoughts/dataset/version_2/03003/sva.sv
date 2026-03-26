module DAC_8BIT_sva (
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic d4,
    input logic d5,
    input logic d6,
    input logic d7,
    input logic out_v
);

    // Output must equal the OR of all input bits.
    check_out_matches_or_reduce: assert property (
        @($global_clock) out_v == (d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7)
    );

    // d0 high must force the output high.
    check_d0_drives_output_high: assert property (
        @($global_clock) d0 |-> out_v
    );

    // d1 high must force the output high.
    check_d1_drives_output_high: assert property (
        @($global_clock) d1 |-> out_v
    );

    // d2 high must force the output high.
    check_d2_drives_output_high: assert property (
        @($global_clock) d2 |-> out_v
    );

    // d3 high must force the output high.
    check_d3_drives_output_high: assert property (
        @($global_clock) d3 |-> out_v
    );

    // d4 high must force the output high.
    check_d4_drives_output_high: assert property (
        @($global_clock) d4 |-> out_v
    );

    // d5 high must force the output high.
    check_d5_drives_output_high: assert property (
        @($global_clock) d5 |-> out_v
    );

    // d6 high must force the output high.
    check_d6_drives_output_high: assert property (
        @($global_clock) d6 |-> out_v
    );

    // d7 high must force the output high.
    check_d7_drives_output_high: assert property (
        @($global_clock) d7 |-> out_v
    );

    // All inputs low must drive the output low.
    check_all_zero_inputs_drive_output_low: assert property (
        @($global_clock) !(d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7) |-> !out_v
    );

    // A high output must come from at least one high input.
    check_output_high_requires_active_input: assert property (
        @($global_clock) out_v |-> (d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7)
    );

endmodule
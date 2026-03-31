module test_eval_generic_sva (
    input logic [7:0] data,
    input logic       out_bit_def,
    input logic       out_bit_ovr
);

    // out_bit_ovr is high exactly when data[4] is high.
    check_out_bit_ovr_matches_data4: assert property (
        @($global_clock) out_bit_ovr == data[4]
    );

    // out_bit_def is high exactly when data[4] is low.
    check_out_bit_def_matches_data4: assert property (
        @($global_clock) out_bit_def == ~data[4]
    );

    // out_bit_def and out_bit_ovr are never asserted together.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock) !(out_bit_def && out_bit_ovr)
    );

    // A high out_bit_ovr forces out_bit_def low.
    check_ovr_forces_def_low: assert property (
        @($global_clock) out_bit_ovr |-> !out_bit_def
    );

    // A low out_bit_ovr forces out_bit_def high.
    check_no_ovr_forces_def_high: assert property (
        @($global_clock) !out_bit_ovr |-> out_bit_def
    );

endmodule
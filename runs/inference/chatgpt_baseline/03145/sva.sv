module test_eval_generic_sva (
    input logic [7:0] data,
    input logic out_bit_def,
    input logic out_bit_ovr
);

    // out_bit_def is high when the lower nibble is 4 or greater.
    check_out_bit_def_threshold: assert property (
        @($global_clock) out_bit_def == (data[3:0] >= 4'h4)
    );

    // Values below the threshold keep out_bit_def low.
    check_out_bit_def_below_threshold: assert property (
        @($global_clock) (data[3:0] < 4'h4) |-> (out_bit_def == 1'b0)
    );

    // Values at or above the threshold drive out_bit_def high.
    check_out_bit_def_at_or_above_threshold: assert property (
        @($global_clock) (data[3:0] >= 4'h4) |-> (out_bit_def == 1'b1)
    );

    // out_bit_ovr mirrors bit 4 of data.
    check_out_bit_ovr_exact: assert property (
        @($global_clock) out_bit_ovr == data[4]
    );

    // A high data[4] forces out_bit_ovr high.
    check_out_bit_ovr_high: assert property (
        @($global_clock) data[4] |-> (out_bit_ovr == 1'b1)
    );

    // A low data[4] forces out_bit_ovr low.
    check_out_bit_ovr_low: assert property (
        @($global_clock) !data[4] |-> (out_bit_ovr == 1'b0)
    );

endmodule
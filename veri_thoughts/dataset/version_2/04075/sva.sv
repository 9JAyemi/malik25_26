module nand3_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic zn
);

    // If all inputs are high, the NAND output must be low.
    check_all_inputs_high_drive_output_low: assert property (
        @($global_clock) (a && b && c) |-> (zn == 1'b0)
    );

    // If any input is low, the NAND output must be high.
    check_any_input_low_drives_output_high: assert property (
        @($global_clock) ((!a) || (!b) || (!c)) |-> (zn == 1'b1)
    );

    // The output must always match the 3-input NAND function.
    check_output_matches_nand3_function: assert property (
        @($global_clock) (zn == !(a & b & c))
    );

endmodule
module top_module_sva (
    input logic in,
    input logic out
);

    // No clock or reset exists in the RTL; sample this combinational DUT on the formal global clock.

    // Out follows the exact RTL expression.
    check_out_matches_rtl_expression: assert property (
        @($global_clock) out === ((~(in & in)) & 1'b1)
    );

    // The output is the logical inversion of the input.
    check_output_is_inversion_of_input: assert property (
        @($global_clock) out === ~in
    );

    // A low input drives the output high.
    check_low_input_drives_high_output: assert property (
        @($global_clock) (in === 1'b0) |-> (out === 1'b1)
    );

    // A high input drives the output low.
    check_high_input_drives_low_output: assert property (
        @($global_clock) (in === 1'b1) |-> (out === 1'b0)
    );

endmodule
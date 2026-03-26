module top_module_sva (
    input logic a,
    input logic b,
    input logic select,
    input logic out
);

    // Output matches the selected AND/XOR function.
    check_selected_function: assert property (
        @($global_clock) out == ((select == 1'b0) ? (a & b) : (a ^ b))
    );

    // Low select chooses the AND result.
    check_select_low_uses_and: assert property (
        @($global_clock) (select == 1'b0) |-> (out == (a & b))
    );

    // High select chooses the XOR result.
    check_select_high_uses_xor: assert property (
        @($global_clock) (select == 1'b1) |-> (out == (a ^ b))
    );

    // Both low inputs force the output low.
    check_both_inputs_low_drive_zero: assert property (
        @($global_clock) ((a == 1'b0) && (b == 1'b0)) |-> (out == 1'b0)
    );

    // Both high inputs make the output the inverse of select.
    check_both_inputs_high_follow_select: assert property (
        @($global_clock) ((a == 1'b1) && (b == 1'b1)) |-> (out == ~select)
    );

    // Different inputs make the output follow select.
    check_different_inputs_follow_select: assert property (
        @($global_clock) (a != b) |-> (out == select)
    );

endmodule
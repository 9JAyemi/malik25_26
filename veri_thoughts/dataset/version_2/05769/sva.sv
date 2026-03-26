module top_module_sva(
    input logic [1023:0] in,
    input logic [7:0] sel,
    input logic [3:0] out
);

    // Output always matches the selected 4-bit slice.
    check_selected_slice: assert property (
        @($global_clock) out === in[sel*4 +: 4]
    );

    // Selector value 0 picks the lowest nibble.
    check_sel_zero_low_nibble: assert property (
        @($global_clock) (sel == 8'h00) |-> (out === in[3:0])
    );

    // Selector value 128 picks the midpoint nibble.
    check_sel_80_mid_nibble: assert property (
        @($global_clock) (sel == 8'h80) |-> (out === in[515:512])
    );

    // Selector value 255 picks the highest nibble.
    check_sel_ff_high_nibble: assert property (
        @($global_clock) (sel == 8'hFF) |-> (out === in[1023:1020])
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_stable_output: assert property (
        @($global_clock) ($stable(in) && $stable(sel)) |-> $stable(out)
    );

    // A selector change updates the output to the new selected slice.
    check_sel_change_updates_output: assert property (
        @($global_clock) $changed(sel) |-> (out === in[sel*4 +: 4])
    );

endmodule
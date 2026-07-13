module top_module_sva (
    input logic       a,
    input logic       b,
    input logic       sel_b1,
    input logic       sel_b2,
    input logic [7:0] in,
    input logic [7:0] out
);

    // No RTL clock or reset is present; use the global formal clock.
    // The DUT is purely combinational.

    // Output matches the exact RTL combinational expression.
    check_out_matches_rtl_function: assert property (
        @($global_clock)
        out == ((((sel_b1 & sel_b2) ? b : a) == a) ? in : (in & 8'b11100011))
    );

    // When the mux result equals a, the output passes in through unchanged.
    check_out_passthrough_when_mux_equals_a: assert property (
        @($global_clock)
        (((sel_b1 & sel_b2) ? b : a) == a) |-> (out == in)
    );

    // When the mux result differs from a, the output is the masked input.
    check_out_masked_when_mux_differs_from_a: assert property (
        @($global_clock)
        (((sel_b1 & sel_b2) ? b : a) != a) |-> (out == (in & 8'b11100011))
    );

    // If both select signals are not high, the mux chooses a and out equals in.
    check_out_passthrough_when_selects_not_both_high: assert property (
        @($global_clock)
        !(sel_b1 & sel_b2) |-> (out == in)
    );

    // If both select signals are high and a equals b, out still equals in.
    check_out_passthrough_when_selected_inputs_match: assert property (
        @($global_clock)
        (sel_b1 & sel_b2 & (a == b)) |-> (out == in)
    );

    // Upper bits are always passed through because the mask keeps bits [7:5].
    check_upper_bits_always_passthrough: assert property (
        @($global_clock)
        out[7:5] == in[7:5]
    );

    // Lower bits are always passed through because the mask keeps bits [1:0].
    check_lower_bits_always_passthrough: assert property (
        @($global_clock)
        out[1:0] == in[1:0]
    );

    // Middle bits either pass through or clear based on the RTL path select.
    check_middle_bits_follow_path_selection: assert property (
        @($global_clock)
        out[4:2] == ((((sel_b1 & sel_b2) ? b : a) == a) ? in[4:2] : 3'b000)
    );

endmodule
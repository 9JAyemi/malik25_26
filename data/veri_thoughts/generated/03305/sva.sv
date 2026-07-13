module top_module_sva(
    input logic [3:0] data,
    input logic       in,
    input logic       out
);

    // Out implements the top-level combinational function.
    check_out_matches_function: assert property (
        @($global_clock) (out == (in ? data[0] : data[1]))
    );

    // High in selects data[0] through the inverted mux select.
    check_select_data0_when_in_high: assert property (
        @($global_clock) in |-> (out == data[0])
    );

    // Low in selects data[1] through the inverted mux select.
    check_select_data1_when_in_low: assert property (
        @($global_clock) !in |-> (out == data[1])
    );

    // Matching selectable inputs must propagate regardless of in.
    check_equal_lower_bits_propagate: assert property (
        @($global_clock) (data[0] == data[1]) |-> (out == data[0])
    );

    // Out stays stable when in and the two selectable data bits stay stable.
    check_out_stable_when_relevant_inputs_stable: assert property (
        @($global_clock) disable iff ($initstate)
        ($stable(in) && $stable(data[1:0])) |-> $stable(out)
    );

endmodule
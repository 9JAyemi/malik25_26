module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // out must match the RTL mux expression.
    check_mux_function: assert property (
        @($global_clock) out === ((sel == 1'b1) ? b : a)
    );

    // sel high selects b.
    check_select_b_when_sel_high: assert property (
        @($global_clock) (sel == 1'b1) |-> (out === b)
    );

    // sel low selects a.
    check_select_a_when_sel_low: assert property (
        @($global_clock) (sel == 1'b0) |-> (out === a)
    );

    // Equal inputs must produce that same output.
    check_equal_inputs_produce_same_output: assert property (
        @($global_clock) (a === b) |-> (out === a)
    );

endmodule
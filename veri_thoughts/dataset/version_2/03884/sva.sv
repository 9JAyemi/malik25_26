module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

    // Output matches the implemented mux expression.
    check_mux_expression: assert property (
        @($global_clock) out_always === ((sel_b1 & sel_b2) ? b : a)
    );

    // A LOW sel_b1 forces the effective select LOW, so output must be a.
    check_sel_b1_low_routes_a: assert property (
        @($global_clock) (sel_b1 === 1'b0) |-> (out_always === a)
    );

    // A LOW sel_b2 forces the effective select LOW, so output must be a.
    check_sel_b2_low_routes_a: assert property (
        @($global_clock) (sel_b2 === 1'b0) |-> (out_always === a)
    );

    // Both select bits HIGH route b to the output.
    check_both_selects_high_route_b: assert property (
        @($global_clock) ((sel_b1 === 1'b1) && (sel_b2 === 1'b1)) |-> (out_always === b)
    );

endmodule
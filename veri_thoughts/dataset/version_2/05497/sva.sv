module top_module_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

    // When both select bits are high, the output must select b.
    check_output_selects_b_for_sel_11: assert property (
        @($global_clock) (sel_b1 && sel_b2) |-> (out_always == b)
    );

    // When sel_b1 is high and sel_b2 is low, the output must select a.
    check_output_selects_a_for_sel_10: assert property (
        @($global_clock) (sel_b1 && !sel_b2) |-> (out_always == a)
    );

    // When sel_b1 is low and sel_b2 is high, the output must select a.
    check_output_selects_a_for_sel_01: assert property (
        @($global_clock) (!sel_b1 && sel_b2) |-> (out_always == a)
    );

    // When both select bits are low, the output must select a.
    check_output_selects_a_for_sel_00: assert property (
        @($global_clock) (!sel_b1 && !sel_b2) |-> (out_always == a)
    );

    // The output must match the implemented AND-gated 2:1 mux equation.
    check_output_matches_mux_equation: assert property (
        @($global_clock) out_always == ((sel_b1 & sel_b2) ? b : a)
    );

endmodule
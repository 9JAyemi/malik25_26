module comparator_mux_sva (
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [15:0] c,
    input logic        sel,
    input logic [15:0] out,
    input logic        equal
);

    // No explicit clock or reset exists in the RTL; use the global formal clock.

    // out matches the full comparator/mux expression from the RTL.
    check_out_matches_rtl: assert property (
        @($global_clock) out === ((sel == 1'b0) ? ((a > b) ? a : b) : c)
    );

    // equal matches the equality flag expression from the RTL.
    check_equal_matches_rtl: assert property (
        @($global_clock) equal === ((a == b) ? 1'b1 : 1'b0)
    );

    // When sel is low and a is greater than b, out selects a.
    check_out_selects_a_when_a_gt_b: assert property (
        @($global_clock) ((sel == 1'b0) && (a > b)) |-> (out === a)
    );

    // When sel is low and a is less than or equal to b, out selects b.
    check_out_selects_b_when_a_lte_b: assert property (
        @($global_clock) ((sel == 1'b0) && (a <= b)) |-> (out === b)
    );

    // When sel is high, out selects c.
    check_out_selects_c_when_sel_high: assert property (
        @($global_clock) (sel == 1'b1) |-> (out === c)
    );

    // When a and b are equal, the equal flag is asserted.
    check_equal_asserts_on_equal_inputs: assert property (
        @($global_clock) (a == b) |-> (equal === 1'b1)
    );

    // When a and b differ, the equal flag is deasserted.
    check_equal_deasserts_on_unequal_inputs: assert property (
        @($global_clock) (a != b) |-> (equal === 1'b0)
    );

endmodule
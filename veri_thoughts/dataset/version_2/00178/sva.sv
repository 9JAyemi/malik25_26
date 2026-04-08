module my_module_assertions (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic out
);

    // out matches the exact RTL expression.
    check_out_matches_rtl_function: assert property (
        @($global_clock)
        out === ((D == 1'b1) ? ~((B == 1'b1) ? A : C) : ((B == 1'b1) ? A : C))
    );

    // When B selects A and D is low, out equals A.
    check_select_a_no_invert: assert property (
        @($global_clock)
        ((B === 1'b1) && (D === 1'b0)) |-> (out === A)
    );

    // When B selects C and D is low, out equals C.
    check_select_c_no_invert: assert property (
        @($global_clock)
        ((B === 1'b0) && (D === 1'b0)) |-> (out === C)
    );

    // When B selects A and D is high, out equals inverted A.
    check_select_a_invert: assert property (
        @($global_clock)
        ((B === 1'b1) && (D === 1'b1)) |-> (out === ~A)
    );

    // When B selects C and D is high, out equals inverted C.
    check_select_c_invert: assert property (
        @($global_clock)
        ((B === 1'b0) && (D === 1'b1)) |-> (out === ~C)
    );

endmodule
module same_input_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic out
);
    // out equals 1 iff all three inputs are equal.
    check_function_equivalence: assert property (
        @(posedge $global_clock) out == ((A == B) && (B == C))
    );

    // When all inputs are 1, out must be 1.
    check_all_ones_high: assert property (
        @(posedge $global_clock) ((A == 1'b1) && (B == 1'b1) && (C == 1'b1)) |-> (out == 1'b1)
    );

    // When all inputs are 0, out must be 1.
    check_all_zeros_high: assert property (
        @(posedge $global_clock) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (out == 1'b1)
    );

    // When not all inputs are equal, out must be 0.
    check_not_all_equal_low: assert property (
        @(posedge $global_clock) !((A == B) && (B == C)) |-> (out == 1'b0)
    );

    // If only A and B are equal (and differ from C), out must be 0.
    check_only_AB_equal_low: assert property (
        @(posedge $global_clock) ((A == B) && (A != C)) |-> (out == 1'b0)
    );

    // If only A and C are equal (and differ from B), out must be 0.
    check_only_AC_equal_low: assert property (
        @(posedge $global_clock) ((A == C) && (A != B)) |-> (out == 1'b0)
    );

    // If only B and C are equal (and differ from A), out must be 0.
    check_only_BC_equal_low: assert property (
        @(posedge $global_clock) ((B == C) && (B != A)) |-> (out == 1'b0)
    );

    // Out can be 1 only when all three inputs are equal.
    check_out_high_only_when_all_equal: assert property (
        @(posedge $global_clock) (out == 1'b1) |-> ((A == B) && (B == C))
    );

    // If inputs are stable across a cycle, out must also be stable.
    check_stable_inputs_hold_out_stable: assert property (
        @(posedge $global_clock) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(out)
    );

    // Out can change only if at least one input changes.
    check_out_change_requires_input_change: assert property (
        @(posedge $global_clock) (!$stable(out)) |-> (!$stable(A) || !$stable(B) || !$stable(C))
    );
endmodule
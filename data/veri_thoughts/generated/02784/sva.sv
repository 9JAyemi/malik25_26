module or4_2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // No clock/reset in RTL; combinational OR; sample on $global_clock.

    // X must equal the bitwise OR of A,B,C,D.
    check_or_function_exact: assert property (
        @(posedge $global_clock) X == (A | B | C | D)
    );

    // When all inputs are 0, X must be 0.
    check_all_zero_implies_x_zero: assert property (
        @(posedge $global_clock) (~A & ~B & ~C & ~D) |-> (X == 1'b0)
    );

    // If X is 1, at least one input must be 1.
    check_x_high_implies_any_input_high: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> (A | B | C | D)
    );

    // If A is 1, X must be 1.
    check_a_high_implies_x_high: assert property (
        @(posedge $global_clock) A |-> (X == 1'b1)
    );

    // If B is 1, X must be 1.
    check_b_high_implies_x_high: assert property (
        @(posedge $global_clock) B |-> (X == 1'b1)
    );

    // If C is 1, X must be 1.
    check_c_high_implies_x_high: assert property (
        @(posedge $global_clock) C |-> (X == 1'b1)
    );

    // If D is 1, X must be 1.
    check_d_high_implies_x_high: assert property (
        @(posedge $global_clock) D |-> (X == 1'b1)
    );

    // If inputs are stable, X must be stable.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge $global_clock) $stable({A,B,C,D}) |-> $stable(X)
    );

    // If X was 0 and any input rises, X must become 1.
    check_prev_zero_and_any_input_rose_makes_x_one: assert property (
        @(posedge $global_clock) ($past(X) == 1'b0 && ($rose(A) || $rose(B) || $rose(C) || $rose(D))) |-> (X == 1'b1)
    );

    // If previously only one input was 1 and it falls while others are 0 now, X must be 0.
    check_last_one_fall_causes_x_zero: assert property (
        @(posedge $global_clock)
        (
            ($past( A & ~B & ~C & ~D) && $fell(A) && ~B && ~C && ~D) ||
            ($past(~A &  B & ~C & ~D) && $fell(B) && ~A && ~C && ~D) ||
            ($past(~A & ~B &  C & ~D) && $fell(C) && ~A && ~B && ~D) ||
            ($past(~A & ~B & ~C &  D) && $fell(D) && ~A && ~B && ~C)
        ) |-> (X == 1'b0)
    );

endmodule
module or3_module_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // Output equals the 3-input OR of A, B, C.
    check_or_function: assert property (
        @(posedge clk) disable iff (1'b0) X == (A | B | C)
    );

    // When all inputs are 0, X must be 0.
    check_all_zero_implies_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!A && !B && !C) |-> (X == 1'b0)
    );

    // If any input is 1, X must be 1.
    check_any_one_implies_one: assert property (
        @(posedge clk) disable iff (1'b0) (A || B || C) |-> (X == 1'b1)
    );

    // With B=0 and C=0, X equals A.
    check_pass_through_A_when_others_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!B && !C) |-> (X == A)
    );

    // With A=0 and C=0, X equals B.
    check_pass_through_B_when_others_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!A && !C) |-> (X == B)
    );

    // With A=0 and B=0, X equals C.
    check_pass_through_C_when_others_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!A && !B) |-> (X == C)
    );

    // X can only change when at least one input changes.
    check_output_change_has_input_cause: assert property (
        @(posedge clk) disable iff (1'b0) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C))
    );

    // If inputs are stable across a cycle, X is stable.
    check_stable_output_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(X)
    );

    // A rising edge on X must be caused by a rising edge on some input.
    check_rise_has_rising_input: assert property (
        @(posedge clk) disable iff (1'b0) $rose(X) |-> ($rose(A) || $rose(B) || $rose(C))
    );

    // A falling edge on X must be caused by a falling edge on some input.
    check_fall_has_falling_input: assert property (
        @(posedge clk) disable iff (1'b0) $fell(X) |-> ($fell(A) || $fell(B) || $fell(C))
    );
endmodule
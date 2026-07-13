module mux_2to1_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic X
);
    // When S is 0, output must equal A0.
    check_select0_passes_A0: assert property (
        @(posedge clk) (S === 1'b0) |-> (X === A0)
    );

    // When S is 1, output must equal A1.
    check_select1_passes_A1: assert property (
        @(posedge clk) (S === 1'b1) |-> (X === A1)
    );

    // Functional equivalence with the RTL conditional expression.
    check_functional_equation: assert property (
        @(posedge clk) X === ((S == 1'b0) ? A0 : A1)
    );

    // If A0 and A1 are equal (4-state), X must equal that value regardless of S.
    check_equal_inputs_override: assert property (
        @(posedge clk) (A0 === A1) |-> (X === A0)
    );

    // If inputs and select are stable, output must be stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({S, A0, A1}) |-> $stable(X)
    );

    // With S=0, any change on A0 must be reflected on X.
    check_A0_change_reflected_when_S0: assert property (
        @(posedge clk) (S === 1'b0 && $changed(A0)) |-> (X === A0)
    );

    // With S=1, any change on A1 must be reflected on X.
    check_A1_change_reflected_when_S1: assert property (
        @(posedge clk) (S === 1'b1 && $changed(A1)) |-> (X === A1)
    );

    // If S is unknown and A0!=A1, X must be unknown (x-merge behavior).
    check_unknown_select_diff_inputs_yield_unknown: assert property (
        @(posedge clk) ($isunknown(S) && (A0 !== A1)) |-> $isunknown(X)
    );

    // With S=0 and A0 known, X must be known (and equal to A0).
    check_known_output_when_S0_and_A0_known: assert property (
        @(posedge clk) (S === 1'b0 && !$isunknown(A0)) |-> (!$isunknown(X) && X === A0)
    );

    // With S=1 and A1 known, X must be known (and equal to A1).
    check_known_output_when_S1_and_A1_known: assert property (
        @(posedge clk) (S === 1'b1 && !$isunknown(A1)) |-> (!$isunknown(X) && X === A1)
    );
endmodule
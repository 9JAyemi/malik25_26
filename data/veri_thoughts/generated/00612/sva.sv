module sky130_fd_sc_hdll__and3b_sva (
    input  logic clk,
    input  logic X,
    input  logic A_N,
    input  logic B,
    input  logic C
);
    // X equals (~A_N & B & C).
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((~A_N) & B & C)
    );

    // X high implies B&C are 1 and A_N is 0.
    check_x_high_implies_inputs: assert property (
        @(posedge clk) X |-> (B && C && !A_N)
    );

    // When !A_N & B & C, X must be high.
    check_inputs_imply_x_high: assert property (
        @(posedge clk) (!A_N && B && C) |-> X
    );

    // A_N high forces X low.
    check_an_high_forces_x_low: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // X can only rise when B&C=1 and A_N=0.
    check_rise_requires_inputs_true: assert property (
        @(posedge clk) $rose(X) |-> (B && C && !A_N)
    );

    // X can only fall when at least one disabling input is active.
    check_fall_requires_any_input_false: assert property (
        @(posedge clk) $fell(X) |-> (A_N || !B || !C)
    );

    // Any disabling input active implies X low.
    check_any_disable_implies_x_low: assert property (
        @(posedge clk) (A_N || !B || !C) |-> !X
    );
endmodule
module and4bb_sva (
    input logic clk,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic X
);
    // X equals the bitwise AND of all inputs.
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) (X === (A_N & B_N & C & D))
    );

    // If A_N is 0 then X must be 0.
    check_zero_dominance_A_N: assert property (
        @(posedge clk) disable iff (1'b0) (A_N == 1'b0) |-> (X == 1'b0)
    );

    // If B_N is 0 then X must be 0.
    check_zero_dominance_B_N: assert property (
        @(posedge clk) disable iff (1'b0) (B_N == 1'b0) |-> (X == 1'b0)
    );

    // If C is 0 then X must be 0.
    check_zero_dominance_C: assert property (
        @(posedge clk) disable iff (1'b0) (C == 1'b0) |-> (X == 1'b0)
    );

    // If D is 0 then X must be 0.
    check_zero_dominance_D: assert property (
        @(posedge clk) disable iff (1'b0) (D == 1'b0) |-> (X == 1'b0)
    );

    // If all inputs are 1 then X must be 1.
    check_all_ones_implies_X_one: assert property (
        @(posedge clk) disable iff (1'b0) (A_N && B_N && C && D) |-> (X == 1'b1)
    );

    // If X is 1 then all inputs must be 1.
    check_X_one_implies_all_ones: assert property (
        @(posedge clk) disable iff (1'b0) (X == 1'b1) |-> (A_N && B_N && C && D)
    );

    // If all inputs are stable across a cycle, X must remain stable.
    check_no_state_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
            (A_N == $past(A_N) && B_N == $past(B_N) && C == $past(C) && D == $past(D))
            |-> (X == $past(X))
    );
endmodule
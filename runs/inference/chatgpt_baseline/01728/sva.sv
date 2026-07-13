module mult_select_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    // X equals its defined boolean function.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == ((A1 & A2 & ~B1_N) | (~A1 & (A2 | B1_N)))
    );

    // When B1_N is LOW, X equals A2.
    check_b1n_low_gives_a2: assert property (
        @(posedge CLK) (B1_N == 1'b0) |-> (X == A2)
    );

    // When B1_N is HIGH, X equals ~A1.
    check_b1n_high_gives_not_a1: assert property (
        @(posedge CLK) (B1_N == 1'b1) |-> (X == (~A1))
    );

    // When A1 is LOW, X equals (A2 | B1_N).
    check_a1_low_gives_a2_or_b1n: assert property (
        @(posedge CLK) (A1 == 1'b0) |-> (X == (A2 | B1_N))
    );

    // When A1 is HIGH, X equals (A2 & ~B1_N).
    check_a1_high_gives_a2_and_not_b1n: assert property (
        @(posedge CLK) (A1 == 1'b1) |-> (X == (A2 & ~B1_N))
    );

    // When A2 is LOW, X equals (~A1 & B1_N).
    check_a2_low_gives_not_a1_and_b1n: assert property (
        @(posedge CLK) (A2 == 1'b0) |-> (X == ((~A1) & B1_N))
    );

    // When A2 is HIGH, X equals (~A1 | ~B1_N).
    check_a2_high_gives_not_a1_or_not_b1n: assert property (
        @(posedge CLK) (A2 == 1'b1) |-> (X == ((~A1) | (~B1_N)))
    );

    // Corner: A1=0, A2=0, B1_N=0 => X=0.
    check_corner_all_zeroes: assert property (
        @(posedge CLK) (A1==1'b0 && A2==1'b0 && B1_N==1'b0) |-> (X==1'b0)
    );

    // Corner: A1=1, A2=1, B1_N=0 => X=1.
    check_corner_a1a2_high_b1n_low: assert property (
        @(posedge CLK) (A1==1'b1 && A2==1'b1 && B1_N==1'b0) |-> (X==1'b1)
    );

    // Corner: A1=1, A2=1, B1_N=1 => X=0.
    check_corner_a1a2_high_b1n_high: assert property (
        @(posedge CLK) (A1==1'b1 && A2==1'b1 && B1_N==1'b1) |-> (X==1'b0)
    );

    // If inputs are stable across a cycle, X is stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge CLK) $stable({A1, A2, B1_N}) |-> $stable(X)
    );

    // If X changes across a cycle, at least one input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) !$stable(X) |-> !$stable({A1, A2, B1_N})
    );
endmodule
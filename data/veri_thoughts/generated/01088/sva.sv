module sky130_fd_sc_ls__nor2b_sva (
    input  logic CLK,
    input  logic Y,
    input  logic A,
    input  logic B_N
);
    // Y equals (~A & B_N) whenever inputs are known.
    check_function_when_inputs_known: assert property (
        @(posedge CLK) (!$isunknown({A,B_N})) |-> (Y == ((~A) & B_N))
    );

    // If A is 1, Y must be 0.
    check_zero_when_A_one: assert property (
        @(posedge CLK) (A == 1'b1) |-> (Y == 1'b0)
    );

    // If B_N is 0, Y must be 0.
    check_zero_when_BN_zero: assert property (
        @(posedge CLK) (B_N == 1'b0) |-> (Y == 1'b0)
    );

    // If A is 0 and B_N is 1, Y must be 1.
    check_one_when_A_zero_BN_one: assert property (
        @(posedge CLK) ((A == 1'b0) && (B_N == 1'b1)) |-> (Y == 1'b1)
    );

    // If Y is 1, then A must be 0 and B_N must be 1.
    check_y_one_implies_A0_BN1: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((A == 1'b0) && (B_N == 1'b1))
    );

    // When B_N is 1, Y equals ~A (4-state aware).
    check_bn_one_implies_y_eq_not_a: assert property (
        @(posedge CLK) (B_N == 1'b1) |-> (Y === (~A))
    );

    // When A is 0, Y equals B_N (4-state aware).
    check_a_zero_implies_y_eq_bn: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y === B_N)
    );

    // If both inputs are stable, output must be stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge CLK) ($stable(A) && $stable(B_N)) |-> $stable(Y)
    );

    // If output changes, at least one input must have changed.
    check_y_change_requires_input_change: assert property (
        @(posedge CLK) (!$stable(Y)) |-> (!$stable(A) || !$stable(B_N))
    );

    // A rise in Y implies A=0 and B_N=1 now.
    check_y_rise_implies_A0_BN1: assert property (
        @(posedge CLK) $rose(Y) |-> ((A == 1'b0) && (B_N == 1'b1))
    );

    // With B_N held at 1, a rising A causes Y to fall.
    check_y_fall_when_A_rose_and_BN1_stable: assert property (
        @(posedge CLK) ($rose(A) && (B_N == 1'b1) && ($past(B_N) == 1'b1)) |-> $fell(Y)
    );

    // With A held at 0, a rising B_N causes Y to rise.
    check_y_rise_when_BN_rose_and_A0_stable: assert property (
        @(posedge CLK) ($rose(B_N) && (A == 1'b0) && ($past(A) == 1'b0)) |-> $rose(Y)
    );
endmodule
module sky130_fd_sc_hdll__o21ba_sva (
    input  logic CLK,
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1_N
);
    // Functional equivalence: X == (~B1_N) & (A1 | A2).
    check_function_equation: assert property (
        @(posedge CLK) X == ((~B1_N) & (A1 | A2))
    );

    // When B1_N is HIGH, X must be LOW.
    check_x_low_when_B1_N_high: assert property (
        @(posedge CLK) (B1_N == 1'b1) |-> (X == 1'b0)
    );

    // When both A1 and A2 are LOW, X must be LOW.
    check_x_low_when_A1_A2_low: assert property (
        @(posedge CLK) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // When B1_N is LOW, X equals (A1 | A2).
    check_x_equals_or_under_enable: assert property (
        @(posedge CLK) (B1_N == 1'b0) |-> (X == (A1 | A2))
    );

    // If X is HIGH, B1_N must be LOW.
    check_x_high_implies_B1_N_low: assert property (
        @(posedge CLK) (X == 1'b1) |-> (B1_N == 1'b0)
    );

    // If X is HIGH, at least one of A1 or A2 must be HIGH.
    check_x_high_implies_A1_or_A2_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A1 || A2)
    );

    // If B1_N is LOW and A1 is HIGH, X must be HIGH.
    check_x_high_when_B1_N_low_and_A1_high: assert property (
        @(posedge CLK) ((B1_N == 1'b0) && (A1 == 1'b1)) |-> (X == 1'b1)
    );

    // If B1_N is LOW and A2 is HIGH, X must be HIGH.
    check_x_high_when_B1_N_low_and_A2_high: assert property (
        @(posedge CLK) ((B1_N == 1'b0) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    // If B1_N is LOW and both A1 and A2 are LOW, X must be LOW.
    check_x_low_when_enable_and_inputs_low: assert property (
        @(posedge CLK) ((B1_N == 1'b0) && (A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // If X is LOW, then either B1_N is HIGH or both A1 and A2 are LOW.
    check_x_low_implies_block_or_both_low: assert property (
        @(posedge CLK) (X == 1'b0) |-> (B1_N || ((A1 == 1'b0) && (A2 == 1'b0)))
    );
endmodule
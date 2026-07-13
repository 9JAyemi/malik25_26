module and4_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    // X equals logical AND of all four inputs.
    check_output_equals_and4: assert property (
        @(posedge CLK) X == (A && B && C && D)
    );

    // If X is HIGH, A must be HIGH.
    check_x_high_implies_a_high: assert property (
        @(posedge CLK) X |-> A
    );

    // If X is HIGH, B must be HIGH.
    check_x_high_implies_b_high: assert property (
        @(posedge CLK) X |-> B
    );

    // If X is HIGH, C must be HIGH.
    check_x_high_implies_c_high: assert property (
        @(posedge CLK) X |-> C
    );

    // If X is HIGH, D must be HIGH.
    check_x_high_implies_d_high: assert property (
        @(posedge CLK) X |-> D
    );
endmodule
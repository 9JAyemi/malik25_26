module and4_pg_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X must equal the 4-input AND of A, B, C, and D.
    check_output_matches_and4: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // A high output requires all four inputs to be high.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A && B && C && D)
    );

    // If all four inputs are high, X must be high.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A && B && C && D) |-> X
    );

    // If A is low, X must be low.
    check_a_low_blocks_output: assert property (
        @(posedge clk) !A |-> !X
    );

    // If B is low, X must be low.
    check_b_low_blocks_output: assert property (
        @(posedge clk) !B |-> !X
    );

    // If C is low, X must be low.
    check_c_low_blocks_output: assert property (
        @(posedge clk) !C |-> !X
    );

    // If D is low, X must be low.
    check_d_low_blocks_output: assert property (
        @(posedge clk) !D |-> !X
    );

endmodule
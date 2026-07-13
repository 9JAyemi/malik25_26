module majority_3_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must equal the majority-of-three function.
    check_output_matches_majority: assert property (
        @(posedge clk) X == ((A & B) | (A & C) | (B & C))
    );

    // A and B high together must drive X high.
    check_ab_pair_sets_x: assert property (
        @(posedge clk) (A & B) |-> X
    );

    // A and C high together must drive X high.
    check_ac_pair_sets_x: assert property (
        @(posedge clk) (A & C) |-> X
    );

    // B and C high together must drive X high.
    check_bc_pair_sets_x: assert property (
        @(posedge clk) (B & C) |-> X
    );

    // With no input pair high, X must be low.
    check_no_pair_clears_x: assert property (
        @(posedge clk) (!(A & B) && !(A & C) && !(B & C)) |-> !X
    );

    // A high X requires at least one input pair to be high.
    check_x_requires_two_high_inputs: assert property (
        @(posedge clk) X |-> ((A & B) | (A & C) | (B & C))
    );

endmodule
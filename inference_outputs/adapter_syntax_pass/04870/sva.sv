module logical_and_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must equal the AND of A, B, and C.
    check_y_matches_and: assert property (
        @(posedge clk) Y == (A & B & C)
    );

    // A high Y requires all three inputs to be high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A && B && C)
    );

    // All three high inputs must drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A && B && C) |-> Y
    );

    // A low A must force Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // A low B must force Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // A low C must force Y low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) !C |-> !Y
    );

endmodule
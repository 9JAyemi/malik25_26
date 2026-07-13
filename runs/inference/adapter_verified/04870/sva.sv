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

// A high, B high, and C high must drive Y high.
    check_all_high_drives_y_high: assert property (
        @(posedge clk) (A && B && C) |-> Y
    );

// A low must force Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

// B low must force Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

// C low must force Y low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) !C |-> !Y
    );

// Y high implies all three inputs are high.
    check_y_high_requires_all_high: assert property (
        @(posedge clk) Y |-> (A && B && C)
    );

endmodule

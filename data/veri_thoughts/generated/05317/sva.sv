module nor3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Purely combinational DUT with no native clock or reset; sample on clk.

    // Y matches the implemented gate function.
    check_output_function: assert property (
        @(posedge clk) Y == (C & ~(A & B))
    );

    // C low forces the output low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) !C |-> !Y
    );

    // A and B high force the output low.
    check_ab_high_forces_y_low: assert property (
        @(posedge clk) (A && B) |-> !Y
    );

    // With C high, A low forces the output high.
    check_c_high_a_low_forces_y_high: assert property (
        @(posedge clk) (C && !A) |-> Y
    );

    // With C high, B low forces the output high.
    check_c_high_b_low_forces_y_high: assert property (
        @(posedge clk) (C && !B) |-> Y
    );

    // A high output requires C to be high.
    check_y_high_requires_c_high: assert property (
        @(posedge clk) Y |-> C
    );

    // A high output means A and B are not both high.
    check_y_high_excludes_ab_high: assert property (
        @(posedge clk) Y |-> !(A && B)
    );

    // With C high, a low output implies A and B are both high.
    check_c_high_y_low_requires_ab_high: assert property (
        @(posedge clk) (C && !Y) |-> (A && B)
    );

endmodule
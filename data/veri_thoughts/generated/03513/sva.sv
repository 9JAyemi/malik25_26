module four_to_one_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y must match the RTL Boolean equation.
    check_output_equation: assert property (
        @(posedge clk) Y == (A && B && !C && !D)
    );

    // When A, B, !C, and !D are all true, Y must be high.
    check_y_high_on_match: assert property (
        @(posedge clk) (A && B && !C && !D) |-> Y
    );

    // When the required input combination is not present, Y must be low.
    check_y_low_off_match: assert property (
        @(posedge clk) !(A && B && !C && !D) |-> !Y
    );

endmodule
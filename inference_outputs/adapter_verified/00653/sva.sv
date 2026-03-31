module and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

// X equals the AND of all four inputs.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

// If all inputs are HIGH, X must be HIGH.
    check_all_high_implies_x_high: assert property (
        @(posedge clk) (A & B & C & D) |-> X
    );

// If any input is LOW, X must be LOW.
    check_any_low_implies_x_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !X
    );

// A HIGH X requires all inputs to be HIGH.
    check_x_high_requires_all_high: assert property (
        @(posedge clk) X |-> (A & B & C & D)
    );

// A LOW X implies at least one input is LOW.
    check_x_low_requires_any_low: assert property (
        @(posedge clk) !X |-> (!A || !B || !C || !D)
    );

endmodule

module or3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X matches the OR of A, B, and C.
    check_or3_function: assert property (
        @(posedge clk) X == (A | B | C)
    );

    // If all inputs are low, X must be low.
    check_all_low_gives_low: assert property (
        @(posedge clk) !(A | B | C) |-> !X
    );

    // If any input is high, X must be high.
    check_any_high_gives_high: assert property (
        @(posedge clk) (A | B | C) |-> X
    );

endmodule
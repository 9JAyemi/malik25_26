module four_nor_inv_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y must equal the 4-input NOR of A, B, C, and D.
    check_y_matches_nor_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

    // When all inputs are low, Y must be high.
    check_all_low_drives_y_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

    // When any input is high, Y must be low.
    check_any_high_drives_y_low: assert property (
        @(posedge clk) (A || B || C || D) |-> !Y
    );

    // A high Y implies all inputs are low.
    check_y_high_implies_all_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

    // A low Y implies at least one input is high.
    check_y_low_implies_some_high: assert property (
        @(posedge clk) !Y |-> (A || B || C || D)
    );

endmodule
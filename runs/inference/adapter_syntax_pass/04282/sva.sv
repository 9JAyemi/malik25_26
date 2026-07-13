module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the implemented AND/NOR/BUF logic.
    check_y_matches_logic: assert property (
        @(posedge clk) Y == ~((A1 & A2 & B1) | (A1 & B1))
    );

    // A1 low forces Y high.
    check_a1_low_forces_y_high: assert property (
        @(posedge clk) !A1 |-> Y
    );

    // B1 low forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // A1 and B1 high force Y low.
    check_a1_b1_high_force_y_low: assert property (
        @(posedge clk) (A1 & B1) |-> !Y
    );

    // A1, A2, and B1 high force Y low.
    check_all_three_high_force_y_low: assert property (
        @(posedge clk) (A1 & A2 & B1) |-> !Y
    );

    // A1 and A2 high with B1 low force Y high.
    check_a1_a2_high_b1_low_force_y_high: assert property (
        @(posedge clk) (A1 & A2 & !B1) |-> Y
    );

    // A1 and B1 high with A2 low force Y high.
    check_a1_b1_high_a2_low_force_y_high: assert property (
        @(posedge clk) (A1 & !A2 & B1) |-> Y
    );

endmodule
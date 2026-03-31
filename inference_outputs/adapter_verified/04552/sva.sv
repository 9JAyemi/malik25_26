module logic_function_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

// Y matches the implemented OR-OR-NAND function.
    check_y_function: assert property (
        @(posedge clk) Y == ~( (A1 | A2) & (B1 | B2) & C1 )
    );

// C1 low forces Y high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) !C1 |-> Y
    );

// With C1 high, both A and B pairs low force Y high.
    check_ab_pairs_low_force_y_high: assert property (
        @(posedge clk) C1 && (!A1 && !A2 && !B1 && !B2) |-> Y
    );

// With C1 high, any A pair high with any B pair high forces Y low.
    check_any_ab_pair_high_forces_y_low: assert property (
        @(posedge clk) C1 && ((A1 || A2) && (B1 || B2)) |-> !Y
    );

// A1 high with B1 high with C1 high forces Y low.
    check_a1_b1_high_force_y_low: assert property (
        @(posedge clk) C1 && A1 && B1 |-> !Y
    );

// A2 high with B2 high with C1 high forces Y low.
    check_a2_b2_high_force_y_low: assert property (
        @(posedge clk) C1 && A2 && B2 |-> !Y
    );

// A1 high with B2 high with C1 high forces Y low.
    check_a1_b2_high_force_y_low: assert property (
        @(posedge clk) C1 && A1 && B2 |-> !Y
    );

// A2 high with B1 high with C1 high forces Y low.
    check_a2_b1_high_force_y_low: assert property (
        @(posedge clk) C1 && A2 && B1 |-> !Y
    );

endmodule

module sky130_fd_sc_ms__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

// Y matches the implemented OR-NAND function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2 | A3))
    );

// A high B1 forces Y low.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high A1 forces Y low when B1 is high.
    check_a1_high_forces_y_low_when_b1_high: assert property (
        @(posedge clk) (B1 && A1) |-> !Y
    );

// A high A2 forces Y low when B1 is high.
    check_a2_high_forces_y_low_when_b1_high: assert property (
        @(posedge clk) (B1 && A2) |-> !Y
    );

// A high A3 forces Y low when B1 is high.
    check_a3_high_forces_y_low_when_b1_high: assert property (
        @(posedge clk) (B1 && A3) |-> !Y
    );

// With B1 low, Y is the inverted OR of A1, A2, and A3.
    check_y_high_when_b1_low: assert property (
        @(posedge clk) !B1 |-> Y == !(A1 | A2 | A3)
    );

// With all A inputs low, Y is high.
    check_y_high_when_all_a_low: assert property (
        @(posedge clk) (!A1 && !A2 && !A3) |-> Y
    );

// With B1 low and any A input high, Y is low.
    check_y_low_when_b1_low_and_any_a_high: assert property (
        @(posedge clk) (!B1 && (A1 || A2 || A3)) |-> !Y
    );

endmodule

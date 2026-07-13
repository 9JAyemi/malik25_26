module sky130_fd_sc_ms__o211ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

// Y matches the implemented OR-then-NAND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(C1 & (A1 | A2) & B1)
    );

// A high C1 forces Y low.
    check_c1_forces_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// A high B1 forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// With C1 and B1 low, Y is high.
    check_c1_b1_low_gives_high: assert property (
        @(posedge clk) (!C1 && !B1) |-> Y
    );

// With B1 and A1 low, Y is high.
    check_b1_a1_low_gives_high: assert property (
        @(posedge clk) (!B1 && !A1) |-> Y
    );

// With B1 and A2 low, Y is high.
    check_b1_a2_low_gives_high: assert property (
        @(posedge clk) (!B1 && !A2) |-> Y
    );

// With all three active inputs high, Y is low.
    check_all_active_inputs_low: assert property (
        @(posedge clk) (C1 && B1 && (A1 || A2)) |-> !Y
    );

// A high Y requires C1 and B1 to be low.
    check_high_output_requires_c1_b1_low: assert property (
        @(posedge clk) Y |-> (!C1 && !B1)
    );

// A high Y requires at least one A input high.
    check_high_output_requires_a_input: assert property (
        @(posedge clk) Y |-> (A1 || A2)
    );

endmodule

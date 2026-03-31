module sky130_fd_sc_hvl__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the implemented NOR-of-B1 and the A1/A2 AND term.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2))
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // Both A inputs high force the AND term high and drive Y low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1 low, a low Y requires both A inputs high.
    check_y_low_requires_a1_a2: assert property (
        @(posedge clk) (!B1 && !Y) |-> (A1 && A2)
    );

    // With B1 low, a high Y requires at least one A input low.
    check_y_high_requires_a1_or_a2_low: assert property (
        @(posedge clk) (!B1 && Y) |-> (!A1 || !A2)
    );

    // With both A inputs low, the AND term is low and Y is high.
    check_a1_a2_low_force_y_high: assert property (
        @(posedge clk) (!A1 && !A2) |-> Y
    );

endmodule
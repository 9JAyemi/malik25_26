module sky130_fd_sc_ls__a31oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the NOR of B1 and the three-input AND of A1, A2, and A3.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2 & A3))
    );

    // A high B1 forces the NOR output low.
    check_b1_forces_output_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // With B1 low, all three A inputs high force Y low.
    check_all_a_high_forces_output_low: assert property (
        @(posedge clk) (!B1 && A1 && A2 && A3) |-> !Y
    );

    // With B1 low, A1 low makes the AND term low and Y high.
    check_a1_low_forces_output_high: assert property (
        @(posedge clk) (!B1 && !A1) |-> Y
    );

    // With B1 low, A2 low makes the AND term low and Y high.
    check_a2_low_forces_output_high: assert property (
        @(posedge clk) (!B1 && !A2) |-> Y
    );

    // With B1 low, A3 low makes the AND term low and Y high.
    check_a3_low_forces_output_high: assert property (
        @(posedge clk) (!B1 && !A3) |-> Y
    );

    // If Y is high, B1 must be low and at least one A input must be low.
    check_output_high_conditions: assert property (
        @(posedge clk) Y |-> (!B1 && (!A1 || !A2 || !A3))
    );

    // If Y is low while B1 is low, then all three A inputs must be high.
    check_low_without_b1_requires_all_a_high: assert property (
        @(posedge clk) (!Y && !B1) |-> (A1 && A2 && A3)
    );

endmodule
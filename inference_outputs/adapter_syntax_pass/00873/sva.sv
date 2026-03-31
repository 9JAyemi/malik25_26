module sky130_fd_sc_hd__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented A211OI function.
    check_y_matches_a211oi_function: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1 | C1)
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // A1 and A2 high together force the NOR output low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1 and C1 low, Y is the inverse of A1 AND A2.
    check_y_when_b1_c1_low: assert property (
        @(posedge clk) (!B1 && !C1) |-> (Y == ~(A1 & A2))
    );

    // With A1 and A2 low, Y is the inverse of B1 OR C1.
    check_y_when_a1_a2_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> (Y == ~(B1 | C1))
    );

    // All inputs low produce a high output.
    check_all_inputs_low_gives_y_high: assert property (
        @(posedge clk) (!A1 && !A2 && !B1 && !C1) |-> Y
    );

    // All inputs high produce a low output.
    check_all_inputs_high_gives_y_low: assert property (
        @(posedge clk) (A1 && A2 && B1 && C1) |-> !Y
    );

endmodule
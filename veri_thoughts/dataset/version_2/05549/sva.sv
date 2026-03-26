module sky130_fd_sc_ls__a311oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // Y must match the implemented AOI311 function.
    check_y_matches_a311oi_function: assert property (
        @(posedge clk) Y == ~((A1 & A2 & A3) | B1 | C1)
    );

    // B1 high must force Y low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // C1 high must force Y low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // All three A inputs high must force Y low.
    check_a_triplet_forces_y_low: assert property (
        @(posedge clk) (A1 && A2 && A3) |-> !Y
    );

    // With no asserted NOR inputs, Y must be high.
    check_y_high_when_no_or_term: assert property (
        @(posedge clk) (!B1 && !C1 && !(A1 && A2 && A3)) |-> Y
    );

    // A high Y implies none of the NOR inputs are asserted.
    check_y_high_implies_no_or_term: assert property (
        @(posedge clk) Y |-> (!B1 && !C1 && !(A1 && A2 && A3))
    );

    // If B1 and C1 are low and Y is low, the A triplet must be high.
    check_y_low_without_b1_c1_requires_a_triplet: assert property (
        @(posedge clk) (!B1 && !C1 && !Y) |-> (A1 && A2 && A3)
    );

endmodule
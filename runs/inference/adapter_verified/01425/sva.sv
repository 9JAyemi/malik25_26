module sky130_fd_sc_lp__a311oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

// Y matches the implemented NOR-of-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~((A1 & A2 & A3) | B1 | C1)
    );

// A high B1 forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high C1 forces Y low.
    check_c1_forces_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// All three A inputs high force Y low.
    check_a_triplet_forces_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> !Y
    );

// With B1 and C1 low, Y equals the inverted A-triplet AND.
    check_a_triplet_dominates_when_others_low: assert property (
        @(posedge clk) (!B1 && !C1) |-> (Y == ~(A1 & A2 & A3))
    );

// With the A-triplet low, Y equals the inverted OR of B1 and C1.
    check_or_term_dominates_when_a_triplet_low: assert property (
        @(posedge clk) !(A1 & A2 & A3) |-> (Y == ~(B1 | C1))
    );

// A high Y requires all three A inputs low, B1 low, and C1 low.
    check_y_high_requires_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A1 && !A2 && !A3 && !B1 && !C1)
    );

endmodule

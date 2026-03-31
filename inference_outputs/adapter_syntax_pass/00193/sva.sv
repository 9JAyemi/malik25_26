module sky130_fd_sc_hd__a221oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y matches the implemented NOR-of-ANDs function.
    check_y_matches_nor_of_ands: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // A1 and A2 high together force the NOR output low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // B1 and B2 high together force the NOR output low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // With no active NOR input term, Y must be high.
    check_no_active_term_drives_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> Y
    );

    // A high Y means the C1 term is not active.
    check_y_high_excludes_c1_term: assert property (
        @(posedge clk) Y |-> !C1
    );

    // A high Y means the A1/A2 term is not active.
    check_y_high_excludes_a_pair_term: assert property (
        @(posedge clk) Y |-> !(A1 & A2)
    );

    // A high Y means the B1/B2 term is not active.
    check_y_high_excludes_b_pair_term: assert property (
        @(posedge clk) Y |-> !(B1 & B2)
    );

endmodule
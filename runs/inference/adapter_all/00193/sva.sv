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
    check_y_matches_function: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // B1 and B2 high force the NOR output low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // A1 and A2 high force the NOR output low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // With no active NOR input term, Y is high.
    check_no_active_term_drives_y_high: assert property (
        @(posedge clk) (!C1 && !(B1 & B2) && !(A1 & A2)) |-> Y
    );

    // A high Y means no NOR input term is active.
    check_y_high_means_no_active_term: assert property (
        @(posedge clk) Y |-> (!C1 && !(B1 & B2) && !(A1 & A2))
    );

    // A low Y means at least one NOR input term is active.
    check_y_low_means_active_term: assert property (
        @(posedge clk) !Y |-> (C1 || (B1 & B2) || (A1 & A2))
    );

endmodule
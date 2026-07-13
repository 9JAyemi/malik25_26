module sky130_fd_sc_hdll__a221oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

// Y matches the implemented AOI3 logic.
    check_y_matches_a221oi_function: assert property (
        @(posedge clk) Y == ~(B1 & B2 | C1 | A1 & A2)
    );

// A high C1 forces Y low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// A high A1 and A2 force Y low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// A high B1 and B2 force Y low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

// With no asserted OR/AND path, Y must be high.
    check_no_active_path_sets_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 && A2) && !(B1 && B2)) |-> Y
    );

// A high Y requires all OR/AND paths to be inactive.
    check_y_high_requires_all_paths_inactive: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 && A2) && !(B1 && B2))
    );

endmodule

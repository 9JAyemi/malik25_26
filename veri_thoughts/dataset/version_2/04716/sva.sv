module sky130_fd_sc_ms__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented AOI function.
    check_y_matches_aoi_function: assert property (
        @(posedge clk) Y == ~((A1 & A2 & A3) | (B1 & B2))
    );

    // A-path active forces Y low.
    check_a_product_term_forces_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // B-path active forces Y low.
    check_b_product_term_forces_low: assert property (
        @(posedge clk) (B1 & B2) |-> (Y == 1'b0)
    );

    // If neither product term is active, Y is high.
    check_no_active_product_terms_drives_high: assert property (
        @(posedge clk) (!(A1 & A2 & A3) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // Y low implies at least one product term is active.
    check_y_low_has_active_product_term: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // Y high implies neither product term is active.
    check_y_high_has_no_active_product_term: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!(A1 & A2 & A3) && !(B1 & B2))
    );

endmodule
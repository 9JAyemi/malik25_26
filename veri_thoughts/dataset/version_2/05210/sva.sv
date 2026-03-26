module sky130_fd_sc_ms__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented combinational function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == (!(A1 && A2 && A3) && !(B1 && B2))
    );

    // A1/A2/A3 all high forces Y low.
    check_a_triplet_forces_low: assert property (
        @(posedge clk) (A1 && A2 && A3) |-> !Y
    );

    // B1/B2 both high forces Y low.
    check_b_pair_forces_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

    // If neither input product is active, Y is high.
    check_no_active_product_gives_high: assert property (
        @(posedge clk) (!(A1 && A2 && A3) && !(B1 && B2)) |-> Y
    );

    // Y high means the A-side product is not active.
    check_y_high_blocks_a_triplet: assert property (
        @(posedge clk) Y |-> !(A1 && A2 && A3)
    );

    // Y high means the B-side product is not active.
    check_y_high_blocks_b_pair: assert property (
        @(posedge clk) Y |-> !(B1 && B2)
    );

    // Y low must come from an active A-side or B-side product.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) !Y |-> ((A1 && A2 && A3) || (B1 && B2))
    );

    // All-low inputs produce a high output.
    check_all_low_inputs_high_output: assert property (
        @(posedge clk) (!A1 && !A2 && !A3 && !B1 && !B2) |-> Y
    );

    // All-high inputs produce a low output.
    check_all_high_inputs_low_output: assert property (
        @(posedge clk) (A1 && A2 && A3 && B1 && B2) |-> !Y
    );

endmodule
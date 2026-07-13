module sky130_fd_sc_ms__a2bb2o_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // X matches the implemented NOR/AND/OR function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((~A1_N & ~A2_N) | (B1 & B2))
    );

    // X is high whenever both B inputs are high.
    check_b_inputs_force_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // X is high whenever both A inputs are low.
    check_a_inputs_force_high: assert property (
        @(posedge clk) (~A1_N & ~A2_N) |-> X
    );

    // X is low when neither logic path is active.
    check_no_active_path_means_low: assert property (
        @(posedge clk) ((A1_N | A2_N) & (~B1 | ~B2)) |-> ~X
    );

    // A high X without the B path must come from the A-side NOR path.
    check_high_without_b_path_comes_from_a_path: assert property (
        @(posedge clk) (X & ~(B1 & B2)) |-> (~A1_N & ~A2_N)
    );

    // A high X with the A-side NOR path inactive must come from the B-side AND path.
    check_high_without_a_path_comes_from_b_path: assert property (
        @(posedge clk) (X & (A1_N | A2_N)) |-> (B1 & B2)
    );

    // A low X implies the B-side AND path is inactive.
    check_low_output_disables_b_path: assert property (
        @(posedge clk) (~X) |-> ~(B1 & B2)
    );

    // A low X implies the A-side NOR path is inactive.
    check_low_output_disables_a_path: assert property (
        @(posedge clk) (~X) |-> (A1_N | A2_N)
    );

endmodule
module sky130_fd_sc_ls__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((~(A2 & A1 & A3)) & (~(B2 & B1)))
    );

    // All three A inputs high force Y low.
    check_all_a_high_forces_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> !Y
    );

    // All two B inputs high force Y low.
    check_all_b_high_forces_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // With no A-side block and no B-side block, Y is high.
    check_no_block_on_a_or_b_sets_high: assert property (
        @(posedge clk) ((~(A2 & A1 & A3)) & (~(B2 & B1))) |-> Y
    );

    // A high Y means neither NAND term is blocked.
    check_y_high_requires_no_a_block_and_no_b_block: assert property (
        @(posedge clk) Y |-> ((~(A2 & A1 & A3)) & (~(B2 & B1)))
    );

    // A low Y means at least one NAND term is blocked.
    check_y_low_requires_a_block_or_b_block: assert property (
        @(posedge clk) !Y |-> ((A2 & A1 & A3) | (B2 & B1))
    );

endmodule
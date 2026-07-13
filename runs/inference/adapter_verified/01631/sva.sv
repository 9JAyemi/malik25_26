module sky130_fd_sc_hd__o2bb2a_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

// X matches the implemented NAND/OR/AND logic.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((~A1_N & ~A2_N) & (B1 | B2))
    );

// A high X requires both A inputs low and at least one B input high.
    check_x_high_requires_inputs: assert property (
        @(posedge clk) X |-> ((~A1_N) & (~A2_N) & (B1 | B2))
    );

// Both A inputs low and at least one B input high drive X high.
    check_inputs_enable_x: assert property (
        @(posedge clk) ((~A1_N) & (~A2_N) & (B1 | B2)) |-> X
    );

// A high A1_N forces X low.
    check_a1n_blocks_x: assert property (
        @(posedge clk) A1_N |-> ~X
    );

// A high A2_N forces X low.
    check_a2n_blocks_x: assert property (
        @(posedge clk) A2_N |-> ~X
    );

// A low B1 forces X low.
    check_b1_low_blocks_x: assert property (
        @(posedge clk) ~B1 |-> ~X
    );

// A low B2 forces X low.
    check_b2_low_blocks_x: assert property (
        @(posedge clk) ~B2 |-> ~X
    );

endmodule

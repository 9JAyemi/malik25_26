module sky130_fd_sc_ms__o2111a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // X matches the implemented O2111A logic function.
    check_function_equivalence: assert property (
        @(posedge clk) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // A low B1 input forces the output low.
    check_b1_blocks_output: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // A low C1 input forces the output low.
    check_c1_blocks_output: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // A low D1 input forces the output low.
    check_d1_blocks_output: assert property (
        @(posedge clk) !D1 |-> !X
    );

    // Both A inputs low force the output low.
    check_a_inputs_block_output: assert property (
        @(posedge clk) (!A1 & !A2) |-> !X
    );

    // With B1, C1, and D1 high, A1 can drive the output high.
    check_a1_path_drives_output: assert property (
        @(posedge clk) (A1 & B1 & C1 & D1) |-> X
    );

    // With B1, C1, and D1 high, A2 can drive the output high.
    check_a2_path_drives_output: assert property (
        @(posedge clk) (A2 & B1 & C1 & D1) |-> X
    );

    // A high output implies all required product terms are satisfied.
    check_output_implies_inputs: assert property (
        @(posedge clk) X |-> (B1 & C1 & D1 & (A1 | A2))
    );

endmodule
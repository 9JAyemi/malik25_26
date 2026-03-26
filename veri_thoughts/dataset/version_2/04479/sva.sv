module NAND8_reducer_sva (
    input logic        clk,
    input logic [7:0]  InY,
    input logic        Reduced_NAND
);

    // Output matches the implemented combinational function.
    check_reduced_nand_matches_function: assert property (
        @(posedge clk) Reduced_NAND == (InY == 8'b1000_0000)
    );

    // A high output only occurs for input 8'b10000000.
    check_high_output_requires_exact_pattern: assert property (
        @(posedge clk) Reduced_NAND |-> (InY == 8'b1000_0000)
    );

    // Input 8'b10000000 must drive the output high.
    check_exact_pattern_drives_high_output: assert property (
        @(posedge clk) (InY == 8'b1000_0000) |-> Reduced_NAND
    );

    // Any other input pattern must drive the output low.
    check_nonmatching_pattern_drives_low_output: assert property (
        @(posedge clk) (InY != 8'b1000_0000) |-> !Reduced_NAND
    );

    // Any asserted lower input bit forces the output low.
    check_lower_bits_force_low_output: assert property (
        @(posedge clk) (|InY[6:0]) |-> !Reduced_NAND
    );

    // A low MSB forces the output low.
    check_msb_low_forces_low_output: assert property (
        @(posedge clk) !InY[7] |-> !Reduced_NAND
    );

endmodule
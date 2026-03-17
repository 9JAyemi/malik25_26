module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // F matches the implemented truth table for all sampled inputs.
    check_function_matches_truth_table: assert property (
        @(posedge clk) F == (B ^ C ^ D)
    );

    // When BCD is 000, F must be low.
    check_bcd_000_output_low: assert property (
        @(posedge clk) ({B, C, D} == 3'b000) |-> (F == 1'b0)
    );

    // When BCD is 001, F must be high.
    check_bcd_001_output_high: assert property (
        @(posedge clk) ({B, C, D} == 3'b001) |-> (F == 1'b1)
    );

    // When BCD is 010, F must be high.
    check_bcd_010_output_high: assert property (
        @(posedge clk) ({B, C, D} == 3'b010) |-> (F == 1'b1)
    );

    // When BCD is 011, F must be low.
    check_bcd_011_output_low: assert property (
        @(posedge clk) ({B, C, D} == 3'b011) |-> (F == 1'b0)
    );

    // When BCD is 100, F must be high.
    check_bcd_100_output_high: assert property (
        @(posedge clk) ({B, C, D} == 3'b100) |-> (F == 1'b1)
    );

    // When BCD is 101, F must be low.
    check_bcd_101_output_low: assert property (
        @(posedge clk) ({B, C, D} == 3'b101) |-> (F == 1'b0)
    );

    // When BCD is 110, F must be low.
    check_bcd_110_output_low: assert property (
        @(posedge clk) ({B, C, D} == 3'b110) |-> (F == 1'b0)
    );

    // When BCD is 111, F must be high.
    check_bcd_111_output_high: assert property (
        @(posedge clk) ({B, C, D} == 3'b111) |-> (F == 1'b1)
    );

endmodule
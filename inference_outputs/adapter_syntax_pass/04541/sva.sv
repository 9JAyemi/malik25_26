module twos_complement_sva (
    input logic clk,
    input logic [3:0] Y,
    input logic [3:0] A,
    input logic invert
);

    // Y must always match the RTL's selected expression.
    check_output_matches_rtl: assert property (
        @(posedge clk) Y == (invert ? ~((~A) + 4'b0001) : ((~A) + 4'b0001))
    );

    // In normal mode, Y must equal the inverted input plus one.
    check_normal_mode_output: assert property (
        @(posedge clk) !invert |-> (Y == ((~A) + 4'b0001))
    );

    // In inverted mode, Y must equal the bitwise inverse of the inverted input plus one.
    check_inverted_mode_output: assert property (
        @(posedge clk) invert |-> (Y == ~((~A) + 4'b0001))
    );

    // Zero must remain unchanged in both modes.
    check_zero_input_output: assert property (
        @(posedge clk) (A == 4'h0) |-> (Y == 4'h0)
    );

    // All ones must remain unchanged in both modes.
    check_all_ones_input_output: assert property (
        @(posedge clk) (A == 4'hF) |-> (Y == 4'hF)
    );

    // In normal mode, adding the output back to the input must wrap to zero.
    check_normal_mode_inverse_identity: assert property (
        @(posedge clk) !invert |-> ((Y + A) == 4'h0)
    );

    // In inverted mode, adding the output back to the input must wrap to zero.
    check_inverted_mode_inverse_identity: assert property (
        @(posedge clk) invert |-> ((Y + A) == 4'h0)
    );

endmodule
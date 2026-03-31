module nand_decoder_sva (
    input logic clk,
    input logic [1:0] in,
    input logic [3:0] out
);

    // All four output bits must match the inverted AND of the two inputs.
    check_output_matches_inverted_and: assert property (
        @(posedge clk) out == {4{~(in[0] & in[1])}}
    );

    // If both input bits are high, all outputs must be low.
    check_both_inputs_high_drive_all_outputs_low: assert property (
        @(posedge clk) (in == 2'b11) |-> (out == 4'b0000)
    );

    // If either input bit is low, all outputs must be high.
    check_any_input_low_drives_all_outputs_high: assert property (
        @(posedge clk) (in != 2'b11) |-> (out == 4'b1111)
    );

    // A low output bit implies the two input bits are high.
    check_low_output_implies_both_inputs_high: assert property (
        @(posedge clk) (out[0] == 1'b0) |-> (in == 2'b11)
    );

    // A high output bit implies at least one input bit is low.
    check_high_output_implies_any_input_low: assert property (
        @(posedge clk) (out[0] == 1'b1) |-> (in != 2'b11)
    );

endmodule
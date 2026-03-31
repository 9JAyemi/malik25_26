module final_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [15:0] out,
    input logic [7:0]  out1,
    input logic [7:0]  out2
);

    // out1 is the low byte of the barrel-shifter input.
    check_out1_matches_input_low_byte: assert property (
        @(posedge clk) out1 == in[7:0]
    );

    // out2 is the high byte of the barrel-shifter input.
    check_out2_matches_input_high_byte: assert property (
        @(posedge clk) out2 == in[15:8]
    );

    // The final output is the concatenation of the two barrel-shifter bytes and the stored bit.
    check_out_matches_concatenated_bytes: assert property (
        @(posedge clk) out == {out1, out2, out[0]}
    );

    // The stored bit is the AND of the two barrel-shifter bits.
    check_out0_matches_anded_bits: assert property (
        @(posedge clk) out[0] == (out1[7] & out2[0])
    );

    // A zero low byte forces the stored bit low.
    check_zero_low_byte_forces_zero_out0: assert property (
        @(posedge clk) (in[7:0] == 8'h00) |-> (out[0] == 1'b0)
    );

    // A zero high byte forces the stored bit low.
    check_zero_high_byte_forces_zero_out0: assert property (
        @(posedge clk) (in[15:8] == 8'h00) |-> (out[0] == 1'b0)
    );

    // A zero stored bit implies at least one barrel-shifter bit is low.
    check_zero_out0_implies_zero_source_bit: assert property (
        @(posedge clk) (out[0] == 1'b0) |-> ((out1[7] == 1'b0) || (out2[0] == 1'b0))
    );

    // A high stored bit requires both barrel-shifter bits to be high.
    check_one_out0_requires_one_source_bit: assert property (
        @(posedge clk) (out[0] == 1'b1) |-> ((out1[7] == 1'b1) && (out2[0] == 1'b1))
    );

endmodule
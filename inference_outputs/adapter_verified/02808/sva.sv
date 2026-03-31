module split_16bit_to_8bit_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

// out_hi must equal the upper byte of in.
    check_out_hi_matches_upper_byte: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

// out_lo must equal the lower byte of in.
    check_out_lo_matches_lower_byte: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

// The full output bus must equal the input bus.
    check_full_output_matches_input: assert property (
        @(posedge clk) {out_hi, out_lo} == in
    );

// A zero input must produce zero outputs.
    check_zero_input_produces_zero_outputs: assert property (
        @(posedge clk) (in == 16'h0000) |-> ({out_hi, out_lo} == 16'h0000)
    );

// A zero upper byte must produce zero out_hi.
    check_zero_upper_byte_produces_zero_out_hi: assert property (
        @(posedge clk) (in[15:8] == 8'h00) |-> (out_hi == 8'h00)
    );

// A zero lower byte must produce zero out_lo.
    check_zero_lower_byte_produces_zero_out_lo: assert property (
        @(posedge clk) (in[7:0] == 8'h00) |-> (out_lo == 8'h00)
    );

endmodule

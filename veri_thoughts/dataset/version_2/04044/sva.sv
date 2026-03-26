module decoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [15:0] out
);

    // Output must equal the one-hot decode of the input.
    check_decode_equation: assert property (
        @(posedge clk) out == (16'h0001 << in)
    );

    // Decoder output must always be one-hot.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // The bit selected by the input must be high.
    check_selected_bit_high: assert property (
        @(posedge clk) out[in] == 1'b1
    );

    // Input value 0 must select bit 0.
    check_decode_zero: assert property (
        @(posedge clk) (in == 4'd0) |-> (out == 16'h0001)
    );

    // Input value 15 must select bit 15.
    check_decode_fifteen: assert property (
        @(posedge clk) (in == 4'd15) |-> (out == 16'h8000)
    );

endmodule
module priority_encoder_4bit_sva (
    input logic clk,
    input logic [3:0] I,
    input logic valid,
    input logic [1:0] encoded_value
);

    // valid is high exactly when the input is nonzero.
    check_valid_matches_input: assert property (
        @(posedge clk) (valid == (I != 4'b0000))
    );

    // Zero input produces an invalid result with default encoding.
    check_zero_input_outputs: assert property (
        @(posedge clk) (I == 4'b0000) |-> (valid == 1'b0 && encoded_value == 2'b00)
    );

    // 0001 encodes to 00 and is valid.
    check_encode_0001: assert property (
        @(posedge clk) (I == 4'b0001) |-> (valid == 1'b1 && encoded_value == 2'b00)
    );

    // 0010 encodes to 01 and is valid.
    check_encode_0010: assert property (
        @(posedge clk) (I == 4'b0010) |-> (valid == 1'b1 && encoded_value == 2'b01)
    );

    // 0100 encodes to 10 and is valid.
    check_encode_0100: assert property (
        @(posedge clk) (I == 4'b0100) |-> (valid == 1'b1 && encoded_value == 2'b10)
    );

    // 1000 encodes to 11 and is valid.
    check_encode_1000: assert property (
        @(posedge clk) (I == 4'b1000) |-> (valid == 1'b1 && encoded_value == 2'b11)
    );

    // Any non-one-hot nonzero input uses the default encoding.
    check_default_output_on_non_onehot: assert property (
        @(posedge clk)
        ((I != 4'b0000) &&
         (I != 4'b0001) &&
         (I != 4'b0010) &&
         (I != 4'b0100) &&
         (I != 4'b1000)) |-> (valid == 1'b1 && encoded_value == 2'b00)
    );

endmodule
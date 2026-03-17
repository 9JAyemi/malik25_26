module priority_encoder_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // If input bit 3 is set, it has highest priority and out must be 3.
    check_encode_bit3: assert property (
        @(posedge clk) in[3] |-> (out == 2'b11)
    );

    // If bit 3 is clear and bit 2 is set, out must be 2.
    check_encode_bit2: assert property (
        @(posedge clk) (!in[3] && in[2]) |-> (out == 2'b10)
    );

    // If bits 3:2 are clear and bit 1 is set, out must be 1.
    check_encode_bit1: assert property (
        @(posedge clk) (!in[3] && !in[2] && in[1]) |-> (out == 2'b01)
    );

    // If bits 3:1 are clear and bit 0 is set, out must be 0.
    check_encode_bit0: assert property (
        @(posedge clk) (!in[3] && !in[2] && !in[1] && in[0]) |-> (out == 2'b00)
    );

    // For any nonzero input, out must match the implemented priority encoding.
    check_nonzero_input_encoding: assert property (
        @(posedge clk) (|in) |-> (out == (in[3] ? 2'b11 :
                                         (in[2] ? 2'b10 :
                                          (in[1] ? 2'b01 : 2'b00))))
    );

endmodule
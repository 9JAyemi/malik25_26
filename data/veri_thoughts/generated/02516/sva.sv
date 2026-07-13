module decoder_2to4_sva (
    input logic CLK,
    input logic [1:0] input_bits,
    input logic [3:0] output_bits
);
    // Decoder outputs are a 1-hot decode of input_bits.
    decode_equation: assert property (
        @(posedge CLK) output_bits == (4'b0001 << input_bits)
    );

    // Mapping: input 00 -> output 0001.
    map_in_00: assert property (
        @(posedge CLK) (input_bits == 2'b00) |-> (output_bits == 4'b0001)
    );

    // Mapping: input 01 -> output 0010.
    map_in_01: assert property (
        @(posedge CLK) (input_bits == 2'b01) |-> (output_bits == 4'b0010)
    );

    // Mapping: input 10 -> output 0100.
    map_in_10: assert property (
        @(posedge CLK) (input_bits == 2'b10) |-> (output_bits == 4'b0100)
    );

    // Mapping: input 11 -> output 1000.
    map_in_11: assert property (
        @(posedge CLK) (input_bits == 2'b11) |-> (output_bits == 4'b1000)
    );

    // Reverse mapping: output 0001 implies input 00.
    map_out_0001: assert property (
        @(posedge CLK) (output_bits == 4'b0001) |-> (input_bits == 2'b00)
    );

    // Reverse mapping: output 0010 implies input 01.
    map_out_0010: assert property (
        @(posedge CLK) (output_bits == 4'b0010) |-> (input_bits == 2'b01)
    );

    // Reverse mapping: output 0100 implies input 10.
    map_out_0100: assert property (
        @(posedge CLK) (output_bits == 4'b0100) |-> (input_bits == 2'b10)
    );

    // Reverse mapping: output 1000 implies input 11.
    map_out_1000: assert property (
        @(posedge CLK) (output_bits == 4'b1000) |-> (input_bits == 2'b11)
    );

    // Outputs are at most one-hot (allows all-zero).
    check_onehot0: assert property (
        @(posedge CLK) $onehot0(output_bits)
    );
endmodule
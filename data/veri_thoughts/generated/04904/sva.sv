module DecoGreytoBCD_sva (
    input logic       clk,
    input logic [2:0] entradas_i,
    input logic [2:0] salidas_o
);

    // Output bit 2 is a direct copy of input bit 2.
    check_bit2_passthrough: assert property (
        @(posedge clk) salidas_o[2] == entradas_i[2]
    );

    // Output bit 1 is the XOR of input bits 2 and 1.
    check_bit1_xor_decode: assert property (
        @(posedge clk) salidas_o[1] == (entradas_i[2] ^ entradas_i[1])
    );

    // Output bit 0 is the XOR of output bit 1 and input bit 0.
    check_bit0_chained_xor: assert property (
        @(posedge clk) salidas_o[0] == (salidas_o[1] ^ entradas_i[0])
    );

    // The full output vector matches the implemented Gray-to-binary decode.
    check_full_decode_vector: assert property (
        @(posedge clk) salidas_o == {entradas_i[2], (entradas_i[2] ^ entradas_i[1]), (entradas_i[2] ^ entradas_i[1] ^ entradas_i[0])}
    );

endmodule
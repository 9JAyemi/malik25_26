module expand_key_type_B_256_sva (
    input logic         clk,
    input logic [255:0] in,
    input logic [255:0] out_1,
    input logic [127:0] out_2
);

    function automatic logic [31:0] s4_fn(input logic [31:0] x);
        s4_fn = x ^ (x << 11) ^ (x << 22);
    endfunction

    // The upper four 32-bit words pass through unchanged.
    check_upper_words_passthrough: assert property (
        @(posedge clk) out_1[255:128] == in[255:128]
    );

    // The first transformed lower word is k4 XOR S4(k3).
    check_k4_word_transform: assert property (
        @(posedge clk) out_1[127:96] == (in[127:96] ^ s4_fn(in[159:128]))
    );

    // The second transformed lower word is k4 XOR k5 XOR S4(k3).
    check_k5_word_transform: assert property (
        @(posedge clk) out_1[95:64] == (in[127:96] ^ in[95:64] ^ s4_fn(in[159:128]))
    );

    // The third transformed lower word is k4 XOR k5 XOR k6 XOR S4(k3).
    check_k6_word_transform: assert property (
        @(posedge clk) out_1[63:32] == (in[127:96] ^ in[95:64] ^ in[63:32] ^ s4_fn(in[159:128]))
    );

    // The fourth transformed lower word is k4 XOR k5 XOR k6 XOR k7 XOR S4(k3).
    check_k7_word_transform: assert property (
        @(posedge clk) out_1[31:0] == (in[127:96] ^ in[95:64] ^ in[63:32] ^ in[31:0] ^ s4_fn(in[159:128]))
    );

    // out_2 is the lower 128 bits of out_1.
    check_out2_matches_out1_lower_half: assert property (
        @(posedge clk) out_2 == out_1[127:0]
    );

    // XORing the first two transformed lower words recovers k5.
    check_xor_recovers_k5: assert property (
        @(posedge clk) (out_1[127:96] ^ out_1[95:64]) == in[95:64]
    );

    // XORing the next two transformed lower words recovers k6.
    check_xor_recovers_k6: assert property (
        @(posedge clk) (out_1[95:64] ^ out_1[63:32]) == in[63:32]
    );

    // XORing the last two transformed lower words recovers k7.
    check_xor_recovers_k7: assert property (
        @(posedge clk) (out_1[63:32] ^ out_1[31:0]) == in[31:0]
    );

endmodule
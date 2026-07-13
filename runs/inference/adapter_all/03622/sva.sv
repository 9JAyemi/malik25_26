module key_expander_sva (
    input logic        clk,
    input logic [127:0] key_out,
    input logic [31:0]  g_in,
    input logic [31:0]  g_out,
    input logic [127:0] key_in,
    input logic [3:0]   round,
    input logic         add_w_out,
    input logic         enc_dec
);

    // key_out[127:96] is the first key word XORed with g_func.
    check_key_out_first_word: assert property (
        @(posedge clk)
        key_out[127:96] == (key_in[127:96] ^ {g_out[127:120], g_out[119:112]})
    );

    // key_out[95:64] is the second key word XORed with the previous key word.
    check_key_out_second_word: assert property (
        @(posedge clk)
        key_out[95:64] == (key_in[95:64] ^ key_in[127:96])
    );

    // key_out[63:32] is the third key word XORed with the previous key word.
    check_key_out_third_word: assert property (
        @(posedge clk)
        key_out[63:32] == (key_in[63:32] ^ key_in[95:64])
    );

    // key_out[31:0] is the fourth key word XORed with the previous key word.
    check_key_out_fourth_word: assert property (
        @(posedge clk)
        key_out[31:0] == (key_in[31:0] ^ key_in[63:32])
    );

    // g_in[31:24] is the first rotated input word from key_in[127:96].
    check_g_in_first_word: assert property (
        @(posedge clk)
        g_in[31:24] == key_in[127:120]
    );

    // g_in[23:16] is the second rotated input word from key_in[95:64].
    check_g_in_second_word: assert property (
        @(posedge clk)
        g_in[23:16] == key_in[95:88]
    );

    // g_in[15:8] is the third rotated input word from key_in[63:32].
    check_g_in_third_word: assert property (
        @(posedge clk)
        g_in[15:8] == key_in[63:56]
    );

    // g_in[7:0] is the fourth rotated input word from key_in[31:0].
    check_g_in_fourth_word: assert property (
        @(posedge clk)
        g_in[7:0] == key_in[31:24]
    );

    // round 0 uses the inverse round constant 0x36.
    check_round0_inverse_constant: assert property (
        @(posedge clk)
        (round == 4'd0) |-> (g_out[127:120] == 8'h36)
    );

    // round 1 uses the inverse round constant 0x1b.
    check_round1_inverse_constant: assert property (
        @(posedge clk)
        (round == 4'd1) |-> (g_out[127:120] == 8'h1b)
    );

    // round 8 uses the forward round constant 0x01 shifted by round.
    check_round8_forward_constant: assert property (
        @(posedge clk)
        (round == 4'd8) |-> (g_out[127:120] == (8'h01 << round))
    );

    // round 9 uses the forward round constant 0x36.
    check_round9_forward_constant: assert property (
        @(posedge clk)
        (round == 4'd9) |-> (g_out[127:120] == 8'h36)
    );

endmodule
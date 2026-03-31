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

// key_out[127:96] is the upper 32 bits of key_in.
    check_key_out_upper_bits: assert property (
        @(posedge clk) key_out[127:96] == key_in[127:96]
    );

// key_out[63:32] is the middle 32 bits of key_in.
    check_key_out_middle_bits: assert property (
        @(posedge clk) key_out[63:32] == key_in[63:32]
    );

// key_out[31:0] is the lower 32 bits of key_in.
    check_key_out_lower_bits: assert property (
        @(posedge clk) key_out[31:0] == key_in[31:0]
    );

// g_in is a rotated copy of the upper 32 bits of key_in.
    check_g_in_rotation: assert property (
        @(posedge clk) g_in == {key_in[127:96], key_in[95:64], key_in[63:32], key_in[31:0]}
    );

// g_func is the concatenation of g_out[127:96] and the round constant.
    check_g_func_concat: assert property (
        @(posedge clk) g_func == {g_out[127:96], round_const}
    );

// In encryption mode, rc_dir is 0x1b for round 8 and 0x01 shifted left by round for other rounds.
    check_rc_dir_enc: assert property (
        @(posedge clk) enc_dec |-> (rc_dir == (round == 4'd8 ? 8'h1b : 8'h01 << round))
    );

// In decryption mode, rc_inv is 0x1b for round 1 and 0x80 shifted right by (round - 2) for other rounds.
    check_rc_inv_dec: assert property (
        @(posedge clk) !enc_dec |-> (rc_inv == (round == 4'd1 ? 8'h1b : 8'h80 >> (round - 2)))
    );

// rc selects rc_dir when enc_dec is high and rc_inv when enc_dec is low.
    check_rc_mux: assert property (
        @(posedge clk) rc == (enc_dec ? rc_dir : rc_inv)
    );

// In encryption mode, key_out[95:64] is key_in[95:64] XOR g_func.
    check_key_out_95_64_enc: assert property (
        @(posedge clk) enc_dec |-> (key_out[95:64] == (key_in[95:64] ^ g_func))
    );

// In encryption mode, key_out[63:32] is key_in[63:32] XOR key_in[95:64].
    check_key_out_63_32_enc: assert property (
        @(posedge clk) enc_dec |-> (key_out[63:32] == (key_in[63:32] ^ key_in[95:64]))
    );

// In encryption mode, key_out[31:0] is key_in[31:0] XOR key_in[63:32].
    check_key_out_31_0_enc: assert property (
        @(posedge clk) enc_dec |-> (key_out[31:0] == (key_in[31:0] ^ key_in[63:32]))
    );

// In decryption mode, key_out[95:64] is key_in[95:64] XOR g_func XOR key_in[63:32].
    check_key_out_95_64_dec: assert property (
        @(posedge clk) !enc_dec |-> (key_out[95:64] == (key_in[95:64] ^ g_func ^ key_in[63:32]))
    );

// In decryption mode, key_out[63:32] is key_in[63:32] XOR key_in[95:64].
    check_key_out_63_32_dec: assert property (
        @(posedge clk) !enc_dec |-> (key_out[63:32] == (key_in[63:32] ^ key_in[95:64]))
    );

// In decryption mode, key_out[31:0] is key_in[31:0] XOR key_in[63:32].
    check_key_out_31_0_dec: assert property (
        @(posedge clk) !enc_dec |-> (key_out[31:0] == (key_in[31:0] ^ key_in[63:32]))
    );

endmodule

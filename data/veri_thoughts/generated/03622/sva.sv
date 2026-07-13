module key_expander_sva (
    input logic         clk,
    input logic [127:0] key_out,
    input logic [31:0]  g_in,
    input logic [31:0]  g_out,
    input logic [127:0] key_in,
    input logic [3:0]   round,
    input logic         add_w_out,
    input logic         enc_dec
);

    function automatic logic [7:0] rc_expected (
        input logic       enc_dec_f,
        input logic [3:0] round_f
    );
    begin
        if (enc_dec_f) begin
            if (round_f == 4'd8)
                rc_expected = 8'h1b;
            else if (round_f == 4'd9)
                rc_expected = 8'h36;
            else
                rc_expected = 8'h01 << round_f;
        end
        else begin
            if (round_f == 4'd1)
                rc_expected = 8'h1b;
            else if (round_f == 4'd0)
                rc_expected = 8'h36;
            else
                rc_expected = 8'h80 >> (round_f - 4'd2);
        end
    end
    endfunction

    function automatic logic [31:0] g_func_expected (
        input logic [31:0] g_out_f,
        input logic        enc_dec_f,
        input logic [3:0]  round_f
    );
    begin
        g_func_expected = {g_out_f[31:24] ^ rc_expected(enc_dec_f, round_f), g_out_f[23:0]};
    end
    endfunction

    // g_in is the rotated low key word, xor-augmented with the next word in decrypt mode.
    check_g_in_mapping: assert property (
        @(posedge clk)
        g_in == (enc_dec
                 ? {key_in[23:0], key_in[31:24]}
                 : ({key_in[23:0], key_in[31:24]} ^ {key_in[55:32], key_in[63:56]}))
    );

    // Top output word is the top input word xor the g-function result.
    check_key_out_word0: assert property (
        @(posedge clk)
        key_out[127:96] == (key_in[127:96] ^ g_func_expected(g_out, enc_dec, round))
    );

    // Second output word conditionally includes the g-function result when add_w_out is set.
    check_key_out_word1: assert property (
        @(posedge clk)
        key_out[95:64] == (add_w_out
                           ? (key_in[95:64] ^ key_in[127:96] ^ g_func_expected(g_out, enc_dec, round))
                           : (key_in[95:64] ^ key_in[127:96]))
    );

    // Third output word is the xor of the middle input words.
    check_key_out_word2: assert property (
        @(posedge clk)
        key_out[63:32] == (key_in[63:32] ^ key_in[95:64])
    );

    // Lowest output word is the xor of the low input words.
    check_key_out_word3: assert property (
        @(posedge clk)
        key_out[31:0] == (key_in[31:0] ^ key_in[63:32])
    );

endmodule
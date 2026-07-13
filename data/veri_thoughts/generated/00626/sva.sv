module mix_columns_sva (
    input  logic         CLK,
    input  logic         RESETn,
    input  logic [31:0]  mix_out_enc,
    input  logic [31:0]  mix_out_dec,
    input  logic [31:0]  mix_in
);
    // Combinational DUT with no clock/reset; use CLK/RESETn only for sampling in SVA.

    // Local re-implementation of DUT helper functions
    function automatic logic [7:0] aes_mult_02 (input logic [7:0] data_in);
        aes_mult_02 = (data_in << 1) ^ (({8{data_in[7]}}) & 8'h1b);
    endfunction

    function automatic logic [7:0] aes_mult_04 (input logic [7:0] data_in);
        aes_mult_04 = ((data_in << 2) ^ (({8{data_in[6]}}) & 8'h1b)) ^ (({8{data_in[7]}}) & 8'h36);
    endfunction

    // Byte slices
    logic [7:0] col0, col1, col2, col3;
    assign col0 = mix_in[7:0];
    assign col1 = mix_in[15:8];
    assign col2 = mix_in[23:16];
    assign col3 = mix_in[31:24];

    // Sums used in enc computation
    logic [7:0] sum_p0, sum_p1, sum_p2, sum_p3;
    assign sum_p0 = col1 ^ col2 ^ col3;
    assign sum_p1 = col2 ^ col3 ^ col0;
    assign sum_p2 = col3 ^ col0 ^ col1;
    assign sum_p3 = col0 ^ col1 ^ col2;

    // Expected encryption bytes and 32b value
    logic [7:0] enc0_e, enc1_e, enc2_e, enc3_e;
    assign enc0_e = aes_mult_02(col0 ^ col3) ^ sum_p0;
    assign enc1_e = aes_mult_02(col1 ^ col0) ^ sum_p1;
    assign enc2_e = aes_mult_02(col2 ^ col1) ^ sum_p2;
    assign enc3_e = aes_mult_02(col3 ^ col2) ^ sum_p3;

    logic [31:0] enc_expected;
    assign enc_expected = {enc3_e, enc2_e, enc1_e, enc0_e};

    // Expected decryption XOR pattern from inputs
    logic [7:0] y0, y1, y2;
    assign y0 = aes_mult_04(col2 ^ col0);
    assign y1 = aes_mult_04(col3 ^ col1);
    assign y2 = aes_mult_02(y1 ^ y0);

    logic [15:0] patt16;
    logic [31:0] patt32;
    assign patt16 = { (y2 ^ y1), (y2 ^ y0) };
    assign patt32 = {patt16, patt16};

    // Expected decryption output
    logic [31:0] dec_expected;
    assign dec_expected = enc_expected ^ patt32;

    // Diff between dec and enc (should equal patt32)
    logic [31:0] diff;
    assign diff = mix_out_dec ^ mix_out_enc;

    ///// Functional checks /////
    // mix_out_enc equals the defined AES MixColumns encoding of mix_in.
    check_enc_full: assert property (
        @(posedge CLK) disable iff (!RESETn) mix_out_enc == enc_expected
    );

    // Byte 0 of mix_out_enc matches formula.
    check_enc_byte0: assert property (
        @(posedge CLK) disable iff (!RESETn) mix_out_enc[7:0] == enc0_e
    );

    // Byte 1 of mix_out_enc matches formula.
    check_enc_byte1: assert property (
        @(posedge CLK) disable iff (!RESETn) mix_out_enc[15:8] == enc1_e
    );

    // Byte 2 of mix_out_enc matches formula.
    check_enc_byte2: assert property (
        @(posedge CLK) disable iff (!RESETn) mix_out_enc[23:16] == enc2_e
    );

    // Byte 3 of mix_out_enc matches formula.
    check_enc_byte3: assert property (
        @(posedge CLK) disable iff (!RESETn) mix_out_enc[31:24] == enc3_e
    );

    // mix_out_dec equals mix_out_enc XOR the replicated pattern derived from mix_in.
    check_dec_full: assert property (
        @(posedge CLK) disable iff (!RESETn) mix_out_dec == (mix_out_enc ^ patt32)
    );

    // The XOR difference between dec and enc has identical upper and lower 16-bit halves.
    check_diff_halves_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) diff[31:16] == diff[15:0]
    );

    // The XOR difference byte3 equals byte1 (replication).
    check_diff_byte_pair_high: assert property (
        @(posedge CLK) disable iff (!RESETn) diff[31:24] == diff[15:8]
    );

    // The XOR difference byte2 equals byte0 (replication).
    check_diff_byte_pair_low: assert property (
        @(posedge CLK) disable iff (!RESETn) diff[23:16] == diff[7:0]
    );

    // The low 16 bits of the XOR difference match the computed pattern from mix_in.
    check_diff_low_matches_pattern: assert property (
        @(posedge CLK) disable iff (!RESETn) diff[15:0] == patt16
    );

    // If mix_in is stable across a cycle, both outputs remain stable (pure combinational).
    check_outputs_stable_when_input_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(mix_in) |-> ($stable(mix_out_enc) && $stable(mix_out_dec))
    );
endmodule
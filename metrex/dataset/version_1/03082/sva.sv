// SVA checker for mix_columns
// Binds non-intrusively; no clock required (purely combinational).
// Focuses on functional correctness, X-prop, parity invariants, and corner-case coverage.

bind mix_columns mix_columns_sva i_mix_columns_sva (
  .mix_in     (mix_in),
  .mix_out_enc(mix_out_enc),
  .mix_out_dec(mix_out_dec)
);

module mix_columns_sva
(
  input  logic [31:0] mix_in,
  input  logic [31:0] mix_out_enc,
  input  logic [31:0] mix_out_dec
);

  // Reference Galois multipliers (independent of DUT’s functions)
  function automatic logic [7:0] gf_xtime2 (input logic [7:0] a);
    gf_xtime2 = (a << 1) ^ (8'h1b & {8{a[7]}});
  endfunction

  function automatic logic [7:0] gf_xtime4 (input logic [7:0] a);
    gf_xtime4 = gf_xtime2(gf_xtime2(a));
  endfunction

  // Byte view of inputs
  logic [7:0] b [0:3];
  assign b[0] = mix_in[7:0];
  assign b[1] = mix_in[15:8];
  assign b[2] = mix_in[23:16];
  assign b[3] = mix_in[31:24];

  // Expected encryption bytes
  logic [7:0] e [0:3];
  always_comb begin
    for (int j = 0; j < 4; j++) begin
      logic [7:0] bj    = b[j];
      logic [7:0] bjm1  = b[(j+3)%4];
      logic [7:0] sum_p = b[(j+1)%4] ^ b[(j+2)%4] ^ b[(j+3)%4];
      e[j] = gf_xtime2(bj ^ bjm1) ^ sum_p;
    end
  end

  // Expected encryption and decryption words
  logic [31:0] enc_exp, dec_exp;
  logic [7:0] y0, y1, y2;
  always_comb begin
    enc_exp = {e[3], e[2], e[1], e[0]};

    y0 = gf_xtime4(b[2] ^ b[0]);
    y1 = gf_xtime4(b[3] ^ b[1]);
    y2 = gf_xtime2(y1 ^ y0);

    // {2{A,B}} = {A,B,A,B}
    dec_exp = enc_exp ^ {2{(y2 ^ y1), (y2 ^ y0)}};
  end

  // Core functional checks
  always_comb begin
    assert (mix_out_enc === enc_exp)
      else $error("mix_out_enc mismatch: exp=%0h got=%0h in=%0h", enc_exp, mix_out_enc, mix_in);

    assert (mix_out_dec === dec_exp)
      else $error("mix_out_dec mismatch: exp=%0h got=%0h in=%0h", dec_exp, mix_out_dec, mix_in);
  end

  // Parity (bytewise XOR) invariants (useful linearity sanity checks)
  logic [7:0] xin_par, enc_par, dec_par;
  assign xin_par = b[0] ^ b[1] ^ b[2] ^ b[3];
  assign enc_par = mix_out_enc[31:24] ^ mix_out_enc[23:16] ^ mix_out_enc[15:8] ^ mix_out_enc[7:0];
  assign dec_par = mix_out_dec[31:24] ^ mix_out_dec[23:16] ^ mix_out_dec[15:8] ^ mix_out_dec[7:0];

  always_comb begin
    assert (enc_par === xin_par)
      else $error("enc parity mismatch: in=%0h enc=%0h", xin_par, enc_par);
    assert (dec_par === xin_par)
      else $error("dec parity mismatch: in=%0h dec=%0h", xin_par, dec_par);
  end

  // X/Z propagation: known inputs must produce known outputs
  always_comb begin
    if (!$isunknown(mix_in)) begin
      assert (!$isunknown(mix_out_enc))
        else $error("X/Z detected on mix_out_enc for known mix_in=%0h", mix_in);
      assert (!$isunknown(mix_out_dec))
        else $error("X/Z detected on mix_out_dec for known mix_in=%0h", mix_in);
    end
  end

  // Corner-case coverage (exercise MSB-dependent masks and patterns)
  logic [7:0] t0, t1, t2 [0:3];
  assign t0 = b[2] ^ b[0]; // aes_mult_04 path input #0
  assign t1 = b[3] ^ b[1]; // aes_mult_04 path input #1
  assign t2[0] = b[0] ^ b[3];
  assign t2[1] = b[1] ^ b[0];
  assign t2[2] = b[2] ^ b[1];
  assign t2[3] = b[3] ^ b[2];

  always_comb begin
    // Extremes
    cover (mix_in == 32'h0000_0000);
    cover (mix_in == 32'hFFFF_FFFF);

    // Exercise aes_mult_02 MSB gating via each e[j] input (b[j]^b[j-1]) MSB 0/1
    cover (t2[0][7] == 1'b0); cover (t2[0][7] == 1'b1);
    cover (t2[1][7] == 1'b0); cover (t2[1][7] == 1'b1);
    cover (t2[2][7] == 1'b0); cover (t2[2][7] == 1'b1);
    cover (t2[3][7] == 1'b0); cover (t2[3][7] == 1'b1);

    // Exercise aes_mult_04 dual-mask conditions (depend on bits 7 and 6)
    cover ({t0[7], t0[6]} == 2'b00);
    cover ({t0[7], t0[6]} == 2'b01);
    cover ({t0[7], t0[6]} == 2'b10);
    cover ({t0[7], t0[6]} == 2'b11);

    cover ({t1[7], t1[6]} == 2'b00);
    cover ({t1[7], t1[6]} == 2'b01);
    cover ({t1[7], t1[6]} == 2'b10);
    cover ({t1[7], t1[6]} == 2'b11);
  end

endmodule
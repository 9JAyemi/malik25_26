// Bindable SVA for mix_columns
// Assumes a testbench clock/reset are available. Bind like:
// bind mix_columns mix_columns_sva sva(.clk(clk), .rst_n(rst_n), .mix_in(mix_in), .mix_out_enc(mix_out_enc), .mix_out_dec(mix_out_dec));

module mix_columns_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] mix_in,
  input  logic [31:0] mix_out_enc,
  input  logic [31:0] mix_out_dec
);

  default clocking cb @ (posedge clk); endclocking

  // GF(2^8) reference functions (AES Rijndael polynomial x^8 + x^4 + x^3 + x + 1)
  function automatic [7:0] gf02(input [7:0] x);
    gf02 = (x << 1) ^ ({8{x[7]}} & 8'h1b);
  endfunction

  function automatic [7:0] gf04(input [7:0] x);
    gf04 = (x << 2) ^ ({8{x[6]}} & 8'h1b) ^ ({8{x[7]}} & 8'h36);
  endfunction

  // Reference MixColumns (encryption) for a 32b column
  function automatic [31:0] enc_ref32(input [31:0] m);
    automatic logic [7:0] b0 = m[7:0];
    automatic logic [7:0] b1 = m[15:8];
    automatic logic [7:0] b2 = m[23:16];
    automatic logic [7:0] b3 = m[31:24];
    automatic logic [7:0] sp0 = b1 ^ b2 ^ b3;
    automatic logic [7:0] sp1 = b2 ^ b3 ^ b0;
    automatic logic [7:0] sp2 = b3 ^ b0 ^ b1;
    automatic logic [7:0] sp3 = b0 ^ b1 ^ b2;
    automatic logic [7:0] e0 = gf02(b0 ^ b3) ^ sp0;
    automatic logic [7:0] e1 = gf02(b1 ^ b0) ^ sp1;
    automatic logic [7:0] e2 = gf02(b2 ^ b1) ^ sp2;
    automatic logic [7:0] e3 = gf02(b3 ^ b2) ^ sp3;
    enc_ref32 = {e3, e2, e1, e0};
  endfunction

  // Reference decryption post-mix pattern and full dec output
  function automatic [31:0] dec_ref32(input [31:0] m);
    automatic logic [7:0] b0 = m[7:0];
    automatic logic [7:0] b1 = m[15:8];
    automatic logic [7:0] b2 = m[23:16];
    automatic logic [7:0] b3 = m[31:24];
    automatic logic [7:0] y0 = gf04(b2 ^ b0);
    automatic logic [7:0] y1 = gf04(b3 ^ b1);
    automatic logic [7:0] y2 = gf02(y1 ^ y0);
    automatic logic [31:0] patt = {2{{(y2 ^ y1), (y2 ^ y0)}}};
    dec_ref32 = enc_ref32(m) ^ patt;
  endfunction

  // X/Z sanity
  assert property (disable iff (!rst_n) !$isunknown(mix_in)) else $error("mix_in has X/Z");
  assert property (disable iff (!rst_n) !$isunknown(mix_out_enc)) else $error("mix_out_enc has X/Z");
  assert property (disable iff (!rst_n) !$isunknown(mix_out_dec)) else $error("mix_out_dec has X/Z");

  // Functional correctness
  assert property (disable iff (!rst_n) mix_out_enc == enc_ref32(mix_in))
    else $error("mix_out_enc mismatch vs reference");

  assert property (disable iff (!rst_n) mix_out_dec == dec_ref32(mix_in))
    else $error("mix_out_dec mismatch vs reference");

  // Decryption XOR pattern must be two identical 16b halves
  assert property (disable iff (!rst_n)
                   (mix_out_dec ^ mix_out_enc)[31:16] == (mix_out_dec ^ mix_out_enc)[15:0])
    else $error("replicated 16-bit pattern mismatch in dec path");

  // Coverage: exercise all function branches and key relations
  // Shorthands
  let b0 = mix_in[7:0];
  let b1 = mix_in[15:8];
  let b2 = mix_in[23:16];
  let b3 = mix_in[31:24];
  let x0 = b0 ^ b3;
  let x1 = b1 ^ b0;
  let x2 = b2 ^ b1;
  let x3 = b3 ^ b2;
  let z0 = b2 ^ b0;
  let z1 = b3 ^ b1;
  let patt = mix_out_dec ^ mix_out_enc;

  // gf02 msb=1 seen on any lane
  cover property (disable iff (!rst_n) (x0[7] | x1[7] | x2[7] | x3[7]));
  // gf02 msb=0 on all lanes (at least once)
  cover property (disable iff (!rst_n) !(x0[7] | x1[7] | x2[7] | x3[7]));

  // gf04 branch combos on both operands
  cover property (disable iff (!rst_n) {z0[7], z0[6]} == 2'b00);
  cover property (disable iff (!rst_n) {z0[7], z0[6]} == 2'b01);
  cover property (disable iff (!rst_n) {z0[7], z0[6]} == 2'b10);
  cover property (disable iff (!rst_n) {z0[7], z0[6]} == 2'b11);

  cover property (disable iff (!rst_n) {z1[7], z1[6]} == 2'b00);
  cover property (disable iff (!rst_n) {z1[7], z1[6]} == 2'b01);
  cover property (disable iff (!rst_n) {z1[7], z1[6]} == 2'b10);
  cover property (disable iff (!rst_n) {z1[7], z1[6]} == 2'b11);

  // Ensure both cases where dec==enc and dec!=enc occur
  cover property (disable iff (!rst_n) patt == 32'h0000_0000);
  cover property (disable iff (!rst_n) patt != 32'h0000_0000);

endmodule
// SVA checker for Convolutional_Encoder_Viterbi_Decoder
// Bind this checker to the DUT (no DUT edits needed):
// bind Convolutional_Encoder_Viterbi_Decoder Convolutional_Encoder_Viterbi_Decoder_sva #(k,n,p,m) u_sva (.*);

module Convolutional_Encoder_Viterbi_Decoder_sva #(
  parameter k = 1,
  parameter n = 2,
  parameter p = 2,
  parameter m = 2
)(
  input  logic [k-1:0] in,
  input  logic [n-1:0] enc_out,
  input  logic [k-1:0] dec_out,
  input  logic [p-1:0] shift_reg,
  input  logic [m-1:0] dec_reg
);

  // Reference encode/decode (mirror DUT)
  function automatic [n-1:0] encode_ref(input logic [k-1:0] data);
    case (data)
      0: encode_ref = {1'b1, 1'b0};
      1: encode_ref = {1'b0, 1'b1};
      2: encode_ref = {1'b1, 1'b1};
      3: encode_ref = {1'b0, 1'b0};
      default: encode_ref = 'x;
    endcase
  endfunction

  function automatic [k-1:0] decode_ref(input logic [n-1:0] data);
    if      (data == {1'b1, 1'b0}) decode_ref = {{(k>1)?(k-1):0{1'b0}}, 1'b0};
    else if (data == {1'b0, 1'b1}) decode_ref = {{(k>1)?(k-1):0{1'b0}}, 1'b1};
    else if (data == {1'b1, 1'b1}) decode_ref = {{(k>2)?(k-2):0{1'b0}}, 2'b10};
    else if (data == {1'b0, 1'b0}) decode_ref = {{(k>2)?(k-2):0{1'b0}}, 2'b11};
    else                            decode_ref = 'x;
  endfunction

  // Helpers that match DUT’s truncation/concatenation semantics
  function automatic [p-1:0] enc_shift_fn(input logic [k-1:0] din, input logic [p-1:0] prev);
    if (p == 1) enc_shift_fn = din[0];
    else        enc_shift_fn = {din, prev[p-1:1]}; // auto-truncates to [p-1:0]
  endfunction

  function automatic [m-1:0] dec_shift_fn(input logic [n-1:0] enc, input logic [m-1:0] prev);
    if (m == 1) dec_shift_fn = enc[0];
    else        dec_shift_fn = {enc, prev[m-1:1]}; // auto-truncates to [m-1:0]
  endfunction

  // Parameter sanity (catch width mismatches encoded in DUT)
  initial begin
    assert (n == 2) else $error("DUT expects n==2 (encode/decode use 2-bit codewords)");
    assert (p >= 1) else $error("p must be >=1");
    assert (m >= 1) else $error("m must be >=1");
    // decode() returns 2-bit literals; require k>=2 to avoid truncation
    if (k < 2) $warning("k<2: decode returns 2-bit values truncated to k bits; DUT likely inconsistent");
  end

  // No X/Z on observable outputs when they change
  assert property (@($changed(enc_out)) !$isunknown(enc_out)) else $error("enc_out has X/Z");
  assert property (@($changed(dec_out)) !$isunknown(dec_out)) else $error("dec_out has X/Z");

  // Encoder shift register update correctness
  assert property (@($changed(in)) shift_reg == enc_shift_fn(in, $past(shift_reg)))
    else $error("shift_reg update mismatch");

  // Encoder mapping: enc_out equals encode(shift_reg) after encoder reacts to 'in' change
  assert property (@($changed(in)) enc_out == encode_ref(shift_reg))
    else $error("enc_out != encode(shift_reg)");

  // enc_out only changes in response to input change
  assert property (@($changed(enc_out)) $changed(in))
    else $error("enc_out changed without input change");

  // Decoder shift register update correctness
  assert property (@($changed(enc_out)) dec_reg == dec_shift_fn(enc_out, $past(dec_reg)))
    else $error("dec_reg update mismatch");

  // Decoder mapping: dec_out equals decode(dec_reg) after decoder reacts to enc_out change
  assert property (@($changed(enc_out)) dec_out == decode_ref(dec_reg))
    else $error("dec_out != decode(dec_reg)");

  // dec_out only changes in response to enc_out change
  assert property (@($changed(dec_out)) $changed(enc_out))
    else $error("dec_out changed without enc_out change");

  // enc_out must always be one of the 4 codewords (n==2 required)
  if (n == 2) begin
    assert property (@($changed(in)) enc_out inside {2'b10,2'b01,2'b11,2'b00})
      else $error("enc_out not a valid codeword");
  end

  // dec_out low 2 bits must be one of the decoded symbols; high bits (if any) zero
  if (k >= 2) begin
    assert property (@($changed(enc_out))
                     (dec_out[1:0] inside {2'b00,2'b01,2'b10,2'b11}) &&
                     ((k==2) || (dec_out[k-1:2] == '0)))
      else $error("dec_out not a valid decoded symbol");
  end

  // Coverage: see all codewords and decoded outputs
  if (n == 2) begin
    cover property (@($changed(in)) enc_out == 2'b10);
    cover property (@($changed(in)) enc_out == 2'b01);
    cover property (@($changed(in)) enc_out == 2'b11);
    cover property (@($changed(in)) enc_out == 2'b00);
  end

  if (k >= 2) begin
    cover property (@($changed(enc_out)) dec_out[1:0] == 2'b00);
    cover property (@($changed(enc_out)) dec_out[1:0] == 2'b01);
    cover property (@($changed(enc_out)) dec_out[1:0] == 2'b10);
    cover property (@($changed(enc_out)) dec_out[1:0] == 2'b11);
  end

  // Coverage: shift registers reach all-zeros and all-ones (when possible)
  if (p > 0) begin
    cover property (@($changed(in))  shift_reg == '0);
    cover property (@($changed(in))  shift_reg == {p{1'b1}});
  end
  if (m > 0) begin
    cover property (@($changed(enc_out)) dec_reg == '0);
    cover property (@($changed(enc_out)) dec_reg == {m{1'b1}});
  end

endmodule
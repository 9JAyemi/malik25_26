// SVA bind module for hamming_encoder_decoder
// Focus: correctness of encoding, syndrome, correction index safety, and decode
module hamming_encoder_decoder_sva #(
  parameter int k = 4,
  parameter int n = 7
)(
  input  logic [k-1:0] data_in,
  input  logic [n-1:0] encoded_data,
  input  logic [k-1:0] decoded_data
);

  // Parameter sanity
  initial begin
    assert (k == 4 && n == 7)
      else $error("hamming_encoder_decoder: only (7,4) supported in this SVA (k=4,n=7).");
  end

  // Combinational checks
  always_comb begin
    // X/Z checks (outputs must not be X/Z when inputs are known)
    if (!$isunknown(data_in)) begin
      assert (!$isunknown(encoded_data)) else $error("encoded_data has X/Z with known data_in");
      assert (!$isunknown(decoded_data)) else $error("decoded_data has X/Z with known data_in");
    end

    // Expected parity bits from data_in
    logic p1_exp, p2_exp, p3_exp;
    p1_exp = data_in[0] ^ data_in[1] ^ data_in[3];
    p2_exp = data_in[0] ^ data_in[2] ^ data_in[3];
    p3_exp = data_in[1] ^ data_in[2] ^ data_in[3];

    // Expected encoded vector mapping per DUT
    logic [n-1:0] enc_exp;
    enc_exp = {data_in, p1_exp, p2_exp, p3_exp};

    // Check encoded_data matches expected mapping/values
    assert (encoded_data === enc_exp)
      else $error("encoded_data mismatch vs. expected parity/data mapping");

    // Syndrome computed from encoded_data (per DUT’s equations)
    logic s1, s2, s3;
    s1 = encoded_data[0] ^ encoded_data[1] ^ encoded_data[3] ^ encoded_data[4] ^ encoded_data[6];
    s2 = encoded_data[0] ^ encoded_data[2] ^ encoded_data[3] ^ encoded_data[5] ^ encoded_data[6];
    s3 = encoded_data[1] ^ encoded_data[2] ^ encoded_data[3] ^ encoded_data[6];

    int unsigned idx;
    idx = (s1 ? 1:0) + (s2 ? 2:0) + (s3 ? 4:0);

    // Index safety: either no correction or index within [1..n]
    assert ( (idx == 0) || (idx >= 1 && idx <= n) )
      else $error("correction index out of bounds: %0d (valid: 1..%0d) ", idx, n);

    // If no channel error (encoded_data equals enc_exp), syndrome must be zero
    assert ( !(encoded_data === enc_exp) || (idx == 0) )
      else $error("Non-zero syndrome with a clean codeword");

    // Build expected corrected_data from encoded_data and idx
    logic [n-1:0] corrected_exp;
    corrected_exp = encoded_data;
    if (idx != 0) corrected_exp[idx-1] = ~corrected_exp[idx-1];

    // Expected decode extraction per DUT mapping
    logic [k-1:0] dec_exp;
    dec_exp = {corrected_exp[3], corrected_exp[5], corrected_exp[6], corrected_exp[4]};

    // Decode must match the extraction from corrected codeword
    assert (decoded_data === dec_exp)
      else $error("decoded_data mismatch vs. extracted corrected codeword");

    // With a clean codeword, decoded_data must equal original data_in
    assert ( !(encoded_data === enc_exp) || (decoded_data === data_in) )
      else $error("decoded_data != data_in for clean (no-error) codeword");
  end

  // Simple coverage: observe each possible syndrome index (0..n)
  // Note: With a clean codeword, only 0 is expected.
  generate
    genvar gi;
    for (gi = 0; gi <= n; gi++) begin : cov_idx
      // Immediate cover statement (tool-dependent collection)
      always_comb cover ( ((encoded_data[0] ^ encoded_data[1] ^ encoded_data[3] ^ encoded_data[4] ^ encoded_data[6] ? 1:0) +
                           (encoded_data[0] ^ encoded_data[2] ^ encoded_data[3] ^ encoded_data[5] ^ encoded_data[6] ? 2:0) +
                           (encoded_data[1] ^ encoded_data[2] ^ encoded_data[3] ^ encoded_data[6] ? 4:0)) == gi );
    end
  endgenerate

  // Coverage: clean codeword case
  always_comb cover (encoded_data === {data_in, (data_in[0]^data_in[1]^data_in[3]),
                                       (data_in[0]^data_in[2]^data_in[3]),
                                       (data_in[1]^data_in[2]^data_in[3])});

endmodule

// Bind the SVA module to every instance of the DUT
bind hamming_encoder_decoder
  hamming_encoder_decoder_sva #(.k(k), .n(n))
  hamming_encoder_decoder_sva_i (
    .data_in(data_in),
    .encoded_data(encoded_data),
    .decoded_data(decoded_data)
  );
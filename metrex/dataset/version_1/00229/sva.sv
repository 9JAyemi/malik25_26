// SVA checker for HammingDecoder: spec-accurate Hamming(7,4) decode checks + coverage
module HammingDecoder_sva(input logic [6:0] H, input logic [3:0] D);
  // Correct Hamming(7,4) syndromes (positions 1,2,4 are parity; 3,5,6,7 are data)
  logic s1, s2, s3;           // s1 -> p1(1,3,5,7), s2 -> p2(2,3,6,7), s3 -> p4(4,5,6,7)
  logic [2:0] syn;
  assign s1 = H[0]^H[2]^H[4]^H[6];
  assign s2 = H[1]^H[2]^H[5]^H[6];
  assign s3 = H[3]^H[4]^H[5]^H[6];
  assign syn = {s3,s2,s1};

  // Expected data output per syndrome (flip only when error is in a data bit)
  logic [3:0] expected_D;
  always_comb begin
    expected_D[3] = (syn==3'b111) ? ~H[6] : H[6]; // data bit at pos7
    expected_D[2] = (syn==3'b110) ? ~H[5] : H[5]; // data bit at pos6
    expected_D[1] = (syn==3'b101) ? ~H[4] : H[4]; // data bit at pos5
    expected_D[0] = (syn==3'b011) ? ~H[3] : H[3]; // data bit at pos4
  end

  // Combinational assertions
  always_comb begin
    assert (D === expected_D)
      else $error("HammingDecoder SVA: D mismatch. H=%b syn=%b expected=%b got=%b", H, syn, expected_D, D);
    assert (!$isunknown(D))
      else $error("HammingDecoder SVA: D has X/Z. H=%b D=%b", H, D);
  end

  // Functional coverage of all syndromes and each correction path
  always_comb begin
    cover (syn==3'b000); // no error
    cover (syn==3'b001); // parity bit 1 error
    cover (syn==3'b010); // parity bit 2 error
    cover (syn==3'b100); // parity bit 4 error
    cover (syn==3'b011 && D[0]==~H[3]); // data pos4 corrected
    cover (syn==3'b101 && D[1]==~H[4]); // data pos5 corrected
    cover (syn==3'b110 && D[2]==~H[5]); // data pos6 corrected
    cover (syn==3'b111 && D[3]==~H[6]); // data pos7 corrected
  end
endmodule

// Bind into the DUT
bind HammingDecoder HammingDecoder_sva HammingDecoder_sva_i(.H(H), .D(D));
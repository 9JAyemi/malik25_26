// SVA for hamming_code. Bind this file; no DUT changes required.

module hamming_code_sva;
  // Sample on the global clock (any time advance)
  default clocking cb @ (posedge $global_clock); endclocking

  // Parameter sanity (design hard-codes 4/7 indexing)
  initial assert (n==4 && m==7)
    else $error("Unsupported parameters: n=%0d m=%0d (expected 4), m=%0d (expected 7)", n, m, m);

  // No X/Z on outputs when inputs are known
  assert property (!$isunknown(data_in) |-> (!$isunknown(encoded_data) && !$isunknown(corrected_data)));

  // Encoding equations
  assert property (encoded_data[0] == (data_in[0]^data_in[1]^data_in[3]));
  assert property (encoded_data[1] == (data_in[0]^data_in[2]^data_in[3]));
  assert property (encoded_data[2] ==  data_in[0]);
  assert property (encoded_data[3] == (data_in[1]^data_in[2]^data_in[3]));
  assert property (encoded_data[4] ==  data_in[1]);
  assert property (encoded_data[5] ==  data_in[2]);
  assert property (encoded_data[6] ==  data_in[3]);

  // Parity-check relations (self-consistency of codeword)
  assert property (encoded_data[0] == (encoded_data[2]^encoded_data[4]^encoded_data[6]));
  assert property (encoded_data[1] == (encoded_data[2]^encoded_data[5]^encoded_data[6]));
  assert property (encoded_data[3] == (encoded_data[4]^encoded_data[5]^encoded_data[6]));

  // Syndrome and error signal equations (as implemented)
  assert property (error == (encoded_data[0]^encoded_data[1]^encoded_data[3]^encoded_data[4]^encoded_data[5]^encoded_data[6]));
  assert property (error_position == {
      encoded_data[0]^encoded_data[2]^encoded_data[4]^encoded_data[6],
      encoded_data[1]^encoded_data[2]^encoded_data[5]^encoded_data[6],
      encoded_data[3]^encoded_data[4]^encoded_data[5]^encoded_data[6]
  });

  // End-to-end correctness: decode(encode(data)) == data
  assert property (corrected_data == data_in);

  // Correction mapping vs. syndrome
  assert property (!error |-> corrected_data == {encoded_data[6],encoded_data[5],encoded_data[4],encoded_data[2]});
  assert property ( error |-> corrected_data[0] == (encoded_data[2] ^ (error_position==3'b001)));
  assert property ( error |-> corrected_data[1] == (encoded_data[4] ^ (error_position==3'b010)));
  assert property ( error |-> corrected_data[2] == (encoded_data[5] ^ (error_position==3'b011)));
  assert property ( error |-> corrected_data[3] == (encoded_data[6] ^ (error_position==3'b100)));

  // Optional: error/syndrome consistency (flags potential design issue if violated)
  assert property ( (!error) <-> (error_position==3'b000) );

  // Coverage
  // - All input data patterns
  genvar i;
  generate
    for (i=0; i < (1<<n); i++) begin : cov_all_inputs
      cover property (data_in == i[n-1:0]);
    end
  endgenerate
  // - Parity bits exercise both 0/1
  cover property (encoded_data[0]==1'b0); cover property (encoded_data[0]==1'b1);
  cover property (encoded_data[1]==1'b0); cover property (encoded_data[1]==1'b1);
  cover property (encoded_data[3]==1'b0); cover property (encoded_data[3]==1'b1);
  // - Error flag and syndrome values observed
  cover property (error==1'b0); cover property (error==1'b1);
  genvar s;
  generate
    for (s=0; s<8; s++) begin : cov_syn
      cover property (error_position == s[2:0]);
    end
  endgenerate
endmodule

bind hamming_code hamming_code_sva;
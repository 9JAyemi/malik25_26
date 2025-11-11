// SVA for compression_decompression
// Concise, full functional checks and coverage. Uses bind; no clock required.

module compression_decompression_sva (input [7:0] data_in, input [3:0] data_out);

  // Expected encodings/functions
  function automatic [1:0] calc_code (input [7:0] din);
    if      (din[7:4] == 4'b0000) calc_code = 2'b10;
    else if (din[7:4] == 4'b1111) calc_code = 2'b11;
    else if (din[7:4] == din[3:0]) calc_code = 2'b01;
    else                           calc_code = 2'b00;
  endfunction

  function automatic [3:0] calc_out (input [7:0] din);
    automatic [1:0] c;
    c = calc_code(din);
    calc_out = {c, ( (c==2'b10 || c==2'b11) ? din[7:6] : din[1:0] )};
  endfunction

  // Sanity: knownness propagates
  assert property (!$isunknown(data_in) |-> (!$isunknown(code) && !$isunknown(data_out)))
    else $error("X/Z detected on outputs with known inputs");

  // Core functional equivalence
  assert property (code == calc_code(data_in))
    else $error("code mismatch");

  assert property (data_out == calc_out(data_in))
    else $error("data_out mismatch");

  // Minimal structural check
  assert property (data_out[3:2] == code)
    else $error("data_out[3:2] != code");

  // Functional coverage of all code cases (with priority accounted for)
  cover property (data_in[7:4] == 4'b0000 && code == 2'b10);                 // 10: 0000 prefix (wins over equality)
  cover property (data_in[7:4] == 4'b1111 && code == 2'b11);                 // 11: 1111 prefix (wins over equality)
  cover property (data_in[7:4] == data_in[3:0] &&
                  data_in[7:4] != 4'b0000 && data_in[7:4] != 4'b1111 &&
                  code == 2'b01);                                            // 01: equal nibbles, excluding 0000/1111
  cover property (data_in[7:4] != data_in[3:0] &&
                  data_in[7:4] != 4'b0000 && data_in[7:4] != 4'b1111 &&
                  code == 2'b00);                                            // 00: default

  // Cover lower-bit selection paths
  cover property ((code inside {2'b10,2'b11}) && (data_out[1:0] == data_in[7:6]));
  cover property ((!(code inside {2'b10,2'b11})) && (data_out[1:0] == data_in[1:0]));

endmodule

bind compression_decompression compression_decompression_sva sva_i (.data_in(data_in), .data_out(data_out));
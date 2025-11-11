// SVA for binary_to_7seg. Bind this file to the DUT.
module binary_to_7seg_sva(input logic [3:0] bin_in, input logic [6:0] seg_out);

  // Golden-model function (matches DUT decode)
  function automatic logic [6:0] expected_seg(input logic [3:0] b);
    case (b)
      4'h0: 7'b0011111;
      4'h1: 7'b0000110;
      4'h2: 7'b0101101;
      4'h3: 7'b0100111;
      4'h4: 7'b0110011;
      4'h5: 7'b0111011;
      4'h6: 7'b1111011;
      4'h7: 7'b0001111;
      4'h8: 7'b1111111;
      4'h9: 7'b0111111;
      4'hA: 7'b1011111;
      4'hB: 7'b1111000;
      4'hC: 7'b0011100;
      4'hD: 7'b0101110;
      4'hE: 7'b1111101;
      4'hF: 7'b1110001;
      default: 7'b1111111;
    endcase
  endfunction

  // No X/Z on I/O
  a_no_x_io: assert property (@(bin_in or seg_out) !$isunknown(bin_in) && !$isunknown(seg_out));

  // Functional mapping must be zero-latency w.r.t. bin_in change
  a_map: assert property (@(bin_in) disable iff ($isunknown(bin_in)) ##0 seg_out == expected_seg(bin_in));

  // Output must be one of the 16 legal encodings
  a_valid_enc: assert property (@(seg_out)
    seg_out inside {7'b0011111,7'b0000110,7'b0101101,7'b0100111,
                    7'b0110011,7'b0111011,7'b1111011,7'b0001111,
                    7'b1111111,7'b0111111,7'b1011111,7'b1111000,
                    7'b0011100,7'b0101110,7'b1111101,7'b1110001});

  // No output change unless input changes (no spurious glitches)
  a_no_glitch: assert property (@(seg_out) $changed(seg_out) |-> $changed(bin_in));

  // Optional strong back-map (uniqueness of encoding)
  a_back_0:  assert property (@(seg_out) seg_out==7'b0011111 |-> bin_in==4'h0);
  a_back_1:  assert property (@(seg_out) seg_out==7'b0000110 |-> bin_in==4'h1);
  a_back_2:  assert property (@(seg_out) seg_out==7'b0101101 |-> bin_in==4'h2);
  a_back_3:  assert property (@(seg_out) seg_out==7'b0100111 |-> bin_in==4'h3);
  a_back_4:  assert property (@(seg_out) seg_out==7'b0110011 |-> bin_in==4'h4);
  a_back_5:  assert property (@(seg_out) seg_out==7'b0111011 |-> bin_in==4'h5);
  a_back_6:  assert property (@(seg_out) seg_out==7'b1111011 |-> bin_in==4'h6);
  a_back_7:  assert property (@(seg_out) seg_out==7'b0001111 |-> bin_in==4'h7);
  a_back_8:  assert property (@(seg_out) seg_out==7'b1111111 |-> bin_in==4'h8);
  a_back_9:  assert property (@(seg_out) seg_out==7'b0111111 |-> bin_in==4'h9);
  a_back_A:  assert property (@(seg_out) seg_out==7'b1011111 |-> bin_in==4'hA);
  a_back_B:  assert property (@(seg_out) seg_out==7'b1111000 |-> bin_in==4'hB);
  a_back_C:  assert property (@(seg_out) seg_out==7'b0011100 |-> bin_in==4'hC);
  a_back_D:  assert property (@(seg_out) seg_out==7'b0101110 |-> bin_in==4'hD);
  a_back_E:  assert property (@(seg_out) seg_out==7'b1111101 |-> bin_in==4'hE);
  a_back_F:  assert property (@(seg_out) seg_out==7'b1110001 |-> bin_in==4'hF);

  // Coverage: hit each input code with correct output
  c_0:  cover property (@(bin_in) bin_in==4'h0 && seg_out==expected_seg(4'h0));
  c_1:  cover property (@(bin_in) bin_in==4'h1 && seg_out==expected_seg(4'h1));
  c_2:  cover property (@(bin_in) bin_in==4'h2 && seg_out==expected_seg(4'h2));
  c_3:  cover property (@(bin_in) bin_in==4'h3 && seg_out==expected_seg(4'h3));
  c_4:  cover property (@(bin_in) bin_in==4'h4 && seg_out==expected_seg(4'h4));
  c_5:  cover property (@(bin_in) bin_in==4'h5 && seg_out==expected_seg(4'h5));
  c_6:  cover property (@(bin_in) bin_in==4'h6 && seg_out==expected_seg(4'h6));
  c_7:  cover property (@(bin_in) bin_in==4'h7 && seg_out==expected_seg(4'h7));
  c_8:  cover property (@(bin_in) bin_in==4'h8 && seg_out==expected_seg(4'h8));
  c_9:  cover property (@(bin_in) bin_in==4'h9 && seg_out==expected_seg(4'h9));
  c_A:  cover property (@(bin_in) bin_in==4'hA && seg_out==expected_seg(4'hA));
  c_B:  cover property (@(bin_in) bin_in==4'hB && seg_out==expected_seg(4'hB));
  c_C:  cover property (@(bin_in) bin_in==4'hC && seg_out==expected_seg(4'hC));
  c_D:  cover property (@(bin_in) bin_in==4'hD && seg_out==expected_seg(4'hD));
  c_E:  cover property (@(bin_in) bin_in==4'hE && seg_out==expected_seg(4'hE));
  c_F:  cover property (@(bin_in) bin_in==4'hF && seg_out==expected_seg(4'hF));

endmodule

// Bind to DUT
bind binary_to_7seg binary_to_7seg_sva u_binary_to_7seg_sva(.bin_in(bin_in), .seg_out(seg_out));
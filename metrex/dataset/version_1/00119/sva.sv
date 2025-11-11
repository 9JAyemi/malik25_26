// SVA for bin_to_seven_seg
// Bind into the DUT scope to access ports and internal S2
module bin_to_seven_seg_sva;
  // Accesses D, S, and internal S2 directly via bind scope

  default clocking cb @ (posedge $global_clock); endclocking

  function automatic logic [6:0] s2_map(input logic [3:0] d);
    case (d)
      4'h0: s2_map = 7'b1111110;
      4'h1: s2_map = 7'b0110000;
      4'h2: s2_map = 7'b1101101;
      4'h3: s2_map = 7'b1111001;
      4'h4: s2_map = 7'b0110011;
      4'h5: s2_map = 7'b1011011;
      4'h6: s2_map = 7'b1011111;
      4'h7: s2_map = 7'b1110000;
      4'h8: s2_map = 7'b1111111;
      4'h9: s2_map = 7'b1111011;
      4'hA: s2_map = 7'b1110111;
      4'hB: s2_map = 7'b0011111;
      4'hC: s2_map = 7'b1001110;
      4'hD: s2_map = 7'b0111101;
      4'hE: s2_map = 7'b1001111;
      4'hF: s2_map = 7'b1000111;
      default: s2_map = 7'b0000000;
    endcase
  endfunction

  // Functional correctness
  ap_func:     assert property (S === ~s2_map(D));

  // Internal complement wiring check
  ap_internal: assert property (S === ~S2);

  // Known input => known output
  ap_no_x:     assert property (!$isunknown(D) |-> !$isunknown(S));

  // Unknown input selects default (all off in S2 => all ones on S)
  ap_unk_def:  assert property ($isunknown(D) |-> S === 7'b1111111);

  // Combinational stability: if D is stable, S must be stable
  ap_stable:   assert property ($stable(D) |-> $stable(S));

  // Coverage: all 16 codes observed with correct mapping
  cover_0:  cover property (D==4'h0 && S==~7'b1111110);
  cover_1:  cover property (D==4'h1 && S==~7'b0110000);
  cover_2:  cover property (D==4'h2 && S==~7'b1101101);
  cover_3:  cover property (D==4'h3 && S==~7'b1111001);
  cover_4:  cover property (D==4'h4 && S==~7'b0110011);
  cover_5:  cover property (D==4'h5 && S==~7'b1011011);
  cover_6:  cover property (D==4'h6 && S==~7'b1011111);
  cover_7:  cover property (D==4'h7 && S==~7'b1110000);
  cover_8:  cover property (D==4'h8 && S==~7'b1111111);
  cover_9:  cover property (D==4'h9 && S==~7'b1111011);
  cover_A:  cover property (D==4'hA && S==~7'b1110111);
  cover_B:  cover property (D==4'hB && S==~7'b0011111);
  cover_C:  cover property (D==4'hC && S==~7'b1001110);
  cover_D:  cover property (D==4'hD && S==~7'b0111101);
  cover_E:  cover property (D==4'hE && S==~7'b1001111);
  cover_F:  cover property (D==4'hF && S==~7'b1000111);

  // Coverage: each segment toggles at least once
  genvar b;
  generate
    for (b=0; b<7; b++) begin : seg_cov
      cover property ($changed(S[b]));
    end
  endgenerate
endmodule

bind bin_to_seven_seg bin_to_seven_seg_sva sva();
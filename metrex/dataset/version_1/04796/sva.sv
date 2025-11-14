// SVA for the provided design. Bind these to the DUT for checking/coverage.

// Assertions for counter
module counter_sva;
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_no_x_state: assert property (!$isunknown(state));
  a_no_x_count: assert property (!$isunknown(count));

  // Synchronous reset behavior
  a_reset_vals: assert property (reset |-> (state==S0 && count==4'h0));

  // State sequencing (S0->S1->S2->S3->S0) when not in reset
  a_s0_s1: assert property (disable iff (reset) state==S0 |=> state==S1);
  a_s1_s2: assert property (disable iff (reset) state==S1 |=> state==S2);
  a_s2_s3: assert property (disable iff (reset) state==S2 |=> state==S3);
  a_s3_s0: assert property (disable iff (reset) state==S3 |=> state==S0);

  // Count increments modulo-16 when not in reset
  a_cnt_inc:  assert property (disable iff (reset) count == $past(count)+1);
  a_cnt_wrap: assert property (disable iff (reset) $past(count)==4'hF |-> count==4'h0);

  // Coverage
  c_state_cycle: cover property (disable iff (reset)
                    state==S0 ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0);
  c_cnt_wrap:    cover property (disable iff (reset) $past(count)==4'hF && count==4'h0);
  c_cnt_16step:  cover property (disable iff (reset) count==4'h0 ##16 count==4'h0);
endmodule

bind counter counter_sva counter_sva_i();

// Assertions for top_module (odd_even + 7-seg decode)
module top_sva;
  default clocking cb @(posedge clk); endclocking

  // No X on key observable outputs
  a_no_x_top: assert property (!$isunknown({count, odd_even, seg})));

  // odd_even must track LSB of count
  a_odd_even_map: assert property (odd_even == count[0]);

  // 7-seg decode must match the lookup
  function automatic [6:0] seg_expected(input [3:0] c);
    case (c)
      4'h0: seg_expected = 7'b1000000;
      4'h1: seg_expected = 7'b1111001;
      4'h2: seg_expected = 7'b0100100;
      4'h3: seg_expected = 7'b0110000;
      4'h4: seg_expected = 7'b0011001;
      4'h5: seg_expected = 7'b0010010;
      4'h6: seg_expected = 7'b0000010;
      4'h7: seg_expected = 7'b1111000;
      4'h8: seg_expected = 7'b0000000;
      4'h9: seg_expected = 7'b0011000;
      4'hA: seg_expected = 7'b0001000;
      4'hB: seg_expected = 7'b0000011;
      4'hC: seg_expected = 7'b1000110;
      4'hD: seg_expected = 7'b0100001;
      4'hE: seg_expected = 7'b0000110;
      4'hF: seg_expected = 7'b0001110;
    endcase
  endfunction

  a_seg_map: assert property (seg == seg_expected(count));

  // Coverage
  c_odd_even_toggle: cover property (odd_even ##1 !odd_even ##1 odd_even);
  c_seg_some:        cover property (count==4'h0 ##1 count==4'hA ##1 count==4'hF);
endmodule

bind top_module top_sva top_sva_i();
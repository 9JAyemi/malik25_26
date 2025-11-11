// SVA for hex_7_segment
// Bind this file to the DUT to verify key behavior concisely and with coverage.

module hex_7_segment_sva(
  input  logic        clk,
  input  logic        clr,
  input  logic [15:0] x,
  input  logic [6:0]  a_to_g,
  input  logic [3:0]  an,
  input  logic [1:0]  s,
  input  logic [3:0]  digit,
  input  logic [3:0]  aen,
  input  logic [18:0] clkdiv
);

  default clocking cb @(posedge clk); endclocking

  // 7-seg LUT (must match DUT)
  function automatic logic [6:0] seg_lut (input logic [3:0] d);
    case (d)
      4'h0: seg_lut = 7'b0000001;
      4'h1: seg_lut = 7'b1001111;
      4'h2: seg_lut = 7'b0010010;
      4'h3: seg_lut = 7'b0000110;
      4'h4: seg_lut = 7'b1001100;
      4'h5: seg_lut = 7'b0100100;
      4'h6: seg_lut = 7'b0100000;
      4'h7: seg_lut = 7'b0001111;
      4'h8: seg_lut = 7'b0000000;
      4'h9: seg_lut = 7'b0000100;
      4'hA: seg_lut = 7'b0001000;
      4'hB: seg_lut = 7'b1100000;
      4'hC: seg_lut = 7'b0110001;
      4'hD: seg_lut = 7'b1000010;
      4'hE: seg_lut = 7'b0110000;
      4'hF: seg_lut = 7'b0111000;
      default: seg_lut = 7'b0000001;
    endcase
  endfunction

  // Wiring/derivation checks
  ap_s_matches_clkdiv: assert property (s == clkdiv[18:17]);
  ap_aen_const:        assert property (aen == 4'b1111);
  ap_s_legal:          assert property (s inside {2'b00,2'b01,2'b10,2'b11});

  // Digit muxing by s
  ap_dig_sel0: assert property ((s==2'd0) |-> (digit == x[3:0]));
  ap_dig_sel1: assert property ((s==2'd1) |-> (digit == x[7:4]));
  ap_dig_sel2: assert property ((s==2'd2) |-> (digit == x[11:8]));
  ap_dig_sel3: assert property ((s==2'd3) |-> (digit == x[15:12]));

  // Segment encoding
  ap_seg_map:  assert property (a_to_g == seg_lut(digit));

  // an generation (one-hot at index s, gated by aen)
  ap_an_value: assert property (an == ((4'b0001 << s) & aen));
  ap_an_onehot: assert property ($onehot(an));

  // Reset behavior (asynchronous clear to zero)
  ap_async_clear_now: assert property (@(posedge clr) 1 |-> ##0 (clkdiv==0));
  ap_clear_on_clk:    assert property (clr |-> (clkdiv==0));

  // Divider increments on clk when not clearing (note: ignores mid-cycle async pulses)
  ap_div_incr: assert property (!$past(clr) && !clr |-> clkdiv == $past(clkdiv)+1);

  // Sanity: no X/Z on key I/Os
  ap_no_x: assert property (!$isunknown({a_to_g, an, s, aen}));

  // Coverage
  cv_s_cycle: cover property (s==2'd0 ##1 s==2'd1 ##1 s==2'd2 ##1 s==2'd3);
  cv_each_digit[16]: cover property (digit == cv_each_digit.index[3:0]); // 0..15
  cv_reset: cover property (@(posedge clr) ##0 (clkdiv==0));

endmodule

// Bind into DUT
bind hex_7_segment hex_7_segment_sva i_hex_7_segment_sva (.*);
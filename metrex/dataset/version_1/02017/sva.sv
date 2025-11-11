// SVA for counter_display and submodules
// Quality-focused, concise, with key functional checks and targeted coverage.

package counter_display_sva_pkg;

  function automatic [6:0] sevenseg_decode(input logic [3:0] d);
    case (d)
      4'd0: sevenseg_decode = 7'b1000000;
      4'd1: sevenseg_decode = 7'b1111001;
      4'd2: sevenseg_decode = 7'b0100100;
      4'd3: sevenseg_decode = 7'b0110000;
      4'd4: sevenseg_decode = 7'b0011001;
      4'd5: sevenseg_decode = 7'b0010010;
      4'd6: sevenseg_decode = 7'b0000010;
      4'd7: sevenseg_decode = 7'b1111000;
      4'd8: sevenseg_decode = 7'b0000000;
      4'd9: sevenseg_decode = 7'b0010000;
      default: sevenseg_decode = 7'b1111111;
    endcase
  endfunction

endpackage


// ----------------------------------------------------------------------------
// keyPressed properties
// ----------------------------------------------------------------------------
module keyPressed_sva (input logic clock, reset, enable_in, enable_out);
  import counter_display_sva_pkg::*;

  default clocking cb @(posedge clock); endclocking

  // Exact synchronous pass-through with reset low-true gating
  ap_key_pass: assert property (enable_out == (enable_in && !reset));

  // Coverage
  cp_reset:     cover property (reset ##1 !reset);
  cp_enable_1:  cover property (!reset && enable_in);
  cp_enable_0:  cover property (!reset && !enable_in);

endmodule

bind keyPressed keyPressed_sva keyPressed_sva_i(.clock(clock), .reset(reset),
                                                .enable_in(enable_in), .enable_out(enable_out));


// ----------------------------------------------------------------------------
// counter16bit properties
// ----------------------------------------------------------------------------
module counter16bit_sva (
  input  logic        clock, enable, clear, disp, dir,
  input  logic [3:0]  countValue,
  input  logic [15:0] outputValue
);
  import counter_display_sva_pkg::*;

  default clocking cb @(posedge clock); endclocking

  // Clear dominates
  ap_clear: assert property (clear |=> (countValue == 4'h0 && outputValue == 16'h0000));

  // Hold when not enabled and not clearing
  ap_hold:  assert property (!clear && !enable |=> ($stable(countValue) && $stable(outputValue)));

  // Increment behavior (mod-16), outputValue captures {disp, prev_count} zero-extended
  ap_inc: assert property (!clear && enable && !dir |=> 
                           (countValue == $past(countValue) + 4'd1) &&
                           (outputValue == {11'b0, $past(disp), $past(countValue)}));

  // Decrement behavior (mod-16), same output packing
  ap_dec: assert property (!clear && enable &&  dir |=> 
                           (countValue == $past(countValue) - 4'd1) &&
                           (outputValue == {11'b0, $past(disp), $past(countValue)}));

  // Coverage: both directions, wrap in both directions, disp capture both values
  cp_inc:      cover property (!clear && enable && !dir);
  cp_dec:      cover property (!clear && enable &&  dir);
  cp_wrap_up:  cover property (!clear && enable && !dir &&
                               $past(countValue)==4'hF && countValue==4'h0);
  cp_wrap_dn:  cover property (!clear && enable &&  dir &&
                               $past(countValue)==4'h0 && countValue==4'hF);
  cp_disp1:    cover property (!clear && enable && $past(disp)==1'b1 &&
                               outputValue[4]==1'b1);
  cp_disp0:    cover property (!clear && enable && $past(disp)==1'b0 &&
                               outputValue[4]==1'b0);

endmodule

bind counter16bit counter16bit_sva counter16bit_sva_i(
  .clock(clock), .enable(enable), .clear(clear), .disp(disp), .dir(dir),
  .countValue(countValue), .outputValue(outputValue));


// ----------------------------------------------------------------------------
// Top-level interconnect + display decode checks
// ----------------------------------------------------------------------------
module counter_display_sva;
  import counter_display_sva_pkg::*;

  // Bound into counter_display scope; direct access to names
  // Default clock is system clock
  default clocking cb @(posedge CLOCK_50); endclocking

  // Connectivity assertions (structural sanity)
  a_conn_key_rst:   assert property (K1.reset     == KEY[0]);
  a_conn_key_enin:  assert property (K1.enable_in == KEY[1]);
  a_conn_key_clk:   assert property (K1.clock     == CLOCK_50);
  a_conn_key_out:   assert property (enable       == K1.enable_out);

  a_conn_cnt_clk:   assert property (C1.clock     == CLOCK_50);
  a_conn_cnt_en:    assert property (C1.enable    == enable);
  a_conn_cnt_clr:   assert property (C1.clear     == KEY[0]);
  a_conn_cnt_disp:  assert property (C1.disp      == SW[5]);
  a_conn_cnt_dir:   assert property (C1.dir       == SW[4]);
  a_conn_cnt_val:   assert property (countValue   == C1.countValue);
  a_conn_cnt_hex:   assert property (hexDigits    == C1.outputValue);

  a_conn_seg0:      assert property (S0.digit     == hexDigits[3:0]  && HEX0 == S0.drivers);
  a_conn_seg1:      assert property (S1.digit     == hexDigits[7:4]  && HEX1 == S1.drivers);
  a_conn_seg2:      assert property (S2.digit     == hexDigits[11:8] && HEX2 == S2.drivers);
  a_conn_seg3:      assert property (S3.digit     == hexDigits[15:12]&& HEX3 == S3.drivers);

  // End-to-end: keyPressed function implies enable equals (~reset & KEY[1])
  a_enable_func:    assert property (enable == (KEY[1] && !KEY[0]));

  // End-to-end: Seven-seg decode correctness for all four digits
  a_hex0_decode:    assert property (HEX0 == sevenseg_decode(hexDigits[3:0]));
  a_hex1_decode:    assert property (HEX1 == sevenseg_decode(hexDigits[7:4]));
  a_hex2_decode:    assert property (HEX2 == sevenseg_decode(hexDigits[11:8]));
  a_hex3_decode:    assert property (HEX3 == sevenseg_decode(hexDigits[15:12]));

  // Coverage: reset observed; both directions exercised; error pattern seen on HEX0
  c_top_reset:      cover property (KEY[0]);
  c_top_dir_up:     cover property (!KEY[0] && enable && !SW[4]);
  c_top_dir_dn:     cover property (!KEY[0] && enable &&  SW[4]);
  c_top_err_hex0:   cover property (HEX0 == 7'b1111111);

endmodule

bind counter_display counter_display_sva cd_sva();
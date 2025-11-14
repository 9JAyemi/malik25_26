// SVA for counter
module counter_sva (
  input logic        clk,
  input logic        rst_n,   // active-high async reset (as in DUT)
  input logic        ce,
  input logic        ctrl,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Reset holds counter at 0 on every clk while asserted
  ap_cnt_reset_hold: assert property (rst_n |-> count == 4'd0);

  // Hold when ce deasserted
  ap_cnt_hold:       assert property (!rst_n && !ce  |=> count == $past(count));

  // Count direction when ce asserted
  ap_cnt_inc:        assert property (!rst_n && ce &&  ctrl |=> count == $past(count) + 4'd1);
  ap_cnt_dec:        assert property (!rst_n && ce && !ctrl |=> count == $past(count) - 4'd1);

  // Explicit wrap checks
  ap_cnt_wrap_up:    assert property (!rst_n && ce &&  ctrl && $past(count)==4'hF |=> count==4'h0);
  ap_cnt_wrap_dn:    assert property (!rst_n && ce && !ctrl && $past(count)==4'h0 |=> count==4'hF);

  // Sanity: no X on control/count out of reset
  ap_cnt_no_x:       assert property (!rst_n |-> !$isunknown({ce,ctrl,count}));

  // Coverage
  cv_cnt_wrap_up:    cover  property (!rst_n && ce &&  ctrl && count==4'hF ##1 ce &&  ctrl && count==4'h0);
  cv_cnt_wrap_dn:    cover  property (!rst_n && ce && !ctrl && count==4'h0 ##1 ce && !ctrl && count==4'hF);
endmodule

bind counter counter_sva counter_sva_i (
  .clk(clk), .rst_n(rst_n), .ce(ce), .ctrl(ctrl), .count(count)
);


// SVA for top-level integration + decoder behavior (sampled on top clk)
module top_sva (
  input  logic        clk,
  input  logic        reset,         // active-high reset as wired to counter.rst_n
  input  logic        ce,
  input  logic        ctrl,
  input  logic [11:0] out,
  input  logic [3:0]  counter_out,
  input  logic [15:0] decoder_out,
  input  logic [3:0]  cnt_count      // hierarchical: cnt.count
);
  default clocking cb @(posedge clk); endclocking

  // Connectivity: exposed counter_out equals internal counter state
  ap_cnt_connect:        assert property (counter_out == cnt_count);

  // Decoder mapping (lower nibble one-hot = 1 << SEL), upper bits zero
  ap_dec_upper_zero:     assert property (decoder_out[15:4] == 12'h000);
  ap_out_eq_decoder:     assert property (out == decoder_out[11:0]);
  ap_out_upper_zero:     assert property (out[11:4] == 8'h00);
  ap_out_onehot_map:     assert property (out[3:0] == (4'b0001 << counter_out[1:0]));
  ap_out_onehot:         assert property ($onehot(out[3:0]));

  // During reset, out reflects count==0 -> bit0 set
  ap_out_during_reset:   assert property (reset |-> out == 12'h001);

  // Hold behavior when ce deasserted (out derived only from counter_out)
  ap_out_hold_on_ce0:    assert property (!reset && !ce |=> out == $past(out));

  // Sanity: no X on observable output
  ap_out_no_x:           assert property (!$isunknown(out));

  // Coverage: see all SEL values
  cv_sel0:               cover  property (!reset && counter_out[1:0] == 2'd0);
  cv_sel1:               cover  property (!reset && counter_out[1:0] == 2'd1);
  cv_sel2:               cover  property (!reset && counter_out[1:0] == 2'd2);
  cv_sel3:               cover  property (!reset && counter_out[1:0] == 2'd3);
endmodule

bind top_module top_sva top_sva_i (
  .clk(clk),
  .reset(reset),
  .ce(ce),
  .ctrl(ctrl),
  .out(out),
  .counter_out(counter_out),
  .decoder_out(decoder_out),
  .cnt_count(cnt.count)
)
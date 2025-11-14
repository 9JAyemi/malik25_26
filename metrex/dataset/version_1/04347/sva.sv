// SVA for glitch_filter
// Note: Due to using current-cycle counter values to decide s_tmp, the effective
// debounce length is 5 consecutive identical samples, not 4.

module glitch_filter_sva (
  input  logic        clk,
  input  logic        s_in,
  input  logic        s_out,
  input  logic        s_tmp,          // internal
  input  logic [31:0] counter_low,    // internal
  input  logic [31:0] counter_high    // internal
);
  default clocking cb @ (posedge clk); endclocking

  // Mirror check
  a_out_is_tmp: assert property (s_out == s_tmp);

  // counter_high behavior
  a_high_inc:   assert property (disable iff ($isunknown({s_in,counter_high}))
                                 $past(s_in)    |-> counter_high == $past(counter_high)+1);
  a_high_rst:   assert property (disable iff ($isunknown({s_in,counter_high}))
                                 $past(!s_in)   |-> counter_high == 0);

  // counter_low behavior
  a_low_inc:    assert property (disable iff ($isunknown({s_in,counter_low}))
                                 $past(!s_in)   |-> counter_low == $past(counter_low)+1);
  a_low_rst:    assert property (disable iff ($isunknown({s_in,counter_low}))
                                 $past(s_in)    |-> counter_low == 0);

  // No spurious s_out updates unless a counter hit 4 in the previous cycle
  a_update_only_on_4: assert property (disable iff ($isunknown({counter_low,counter_high,s_out}))
                                       $changed(s_out) |-> ($past(counter_low)==4 || $past(counter_high)==4));

  // Functional intent: s_out changes only after 5 consecutive stable samples
  a_rise_after_5_high: assert property (disable iff ($isunknown({s_in,s_out,counter_low,counter_high}))
                                        $rose(s_out) |->
                                          ( s_in && $past(s_in,1) && $past(s_in,2) && $past(s_in,3) && $past(s_in,4) ) &&
                                          ($past(counter_high)==4) && ($past(counter_low)!=4));

  a_fall_after_5_low:  assert property (disable iff ($isunknown({s_in,s_out,counter_low,counter_high}))
                                        $fell(s_out) |->
                                          ( !s_in && !$past(s_in,1) && !$past(s_in,2) && !$past(s_in,3) && !$past(s_in,4) ) &&
                                          ($past(counter_low)==4) && ($past(counter_high)!=4));

  // If no counter hit 4 last cycle, s_out must hold
  a_no_spurious_hold:  assert property (disable iff ($isunknown({counter_low,counter_high,s_out}))
                                        !($past(counter_low==4) || $past(counter_high==4)) |-> $stable(s_out));

  // Coverage: observe both qualified transitions
  c_rise: cover property (s_in[*4] ##1 (s_in && $rose(s_out)));
  c_fall: cover property (!s_in[*4] ##1 (!s_in && $fell(s_out)));

endmodule

// Bind into DUT
bind glitch_filter glitch_filter_sva gf_sva (
  .clk(clk),
  .s_in(s_in),
  .s_out(s_out),
  .s_tmp(s_tmp),
  .counter_low(counter_low),
  .counter_high(counter_high)
);
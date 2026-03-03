// SVA for counter_4bit
module counter_4bit_sva (
  input logic       clk,
  input logic       rst,
  input logic       en,
  input logic [3:0] out
);
  default clocking @(posedge clk); endclocking

  // Reset clears on next cycle (synchronous reset, priority over en)
  property p_reset_clears; rst |=> (out == 4'h0); endproperty
  assert property (p_reset_clears) else $error("out not cleared after rst");

  // Hold when disabled (no change if rst=0 and en=0)
  property p_hold_when_disabled; (!rst && !en) |=> (out == $past(out)); endproperty
  assert property (p_hold_when_disabled) else $error("out changed while en=0");

  // Increment by 1 when enabled (no wrap case)
  property p_inc_when_enabled_no_wrap;
    (!rst && en && $past(out) != 4'hF) |=> (out == $past(out) + 4'd1);
  endproperty
  assert property (p_inc_when_enabled_no_wrap) else $error("out failed +1 increment");

  // Wrap from 0xF to 0 when enabled
  property p_wrap_when_enabled_on_F;
    (!rst && en && $past(out) == 4'hF) |=> (out == 4'h0);
  endproperty
  assert property (p_wrap_when_enabled_on_F) else $error("out failed wrap 0xF->0");

  // Out changes only due to prior rst or prior en
  property p_only_changes_on_en_or_rst;
    $changed(out) |-> ($past(rst) || (!$past(rst) && $past(en)));
  endproperty
  assert property (p_only_changes_on_en_or_rst) else $error("out changed without rst/en cause");

  // Coverage: observe reset effect, normal increment, wrap, and hold
  cover property (rst |=> out == 4'h0);
  cover property (!rst && en && $past(out) != 4'hF |=> out == $past(out) + 4'd1);
  cover property (!rst && en && $past(out) == 4'hF |=> out == 4'h0);
  cover property (!rst && !en |=> out == $past(out));

  // Coverage: full 16-count cycle under continuous enable (after a reset to 0)
  sequence s_full_cycle;
    rst ##1 (out == 4'h0) ##1 en[*16] ##1 (out == 4'h0);
  endsequence
  cover property (s_full_cycle);

endmodule

// Bind into DUT
bind counter_4bit counter_4bit_sva u_counter_4bit_sva (.clk(clk), .rst(rst), .en(en), .out(out));
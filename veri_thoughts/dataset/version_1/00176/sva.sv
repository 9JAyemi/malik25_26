// SVA for counter_4bit (async active-low reset, sync enable)
module counter_4bit_sva(input logic clk, rst, en, input logic [3:0] out);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_no_x:       assert property (@cb !$isunknown({rst,en,out}));

  // While reset is low at any clock, output must be zero
  a_rst_zero:   assert property (@cb !rst |-> (out == 4'h0));

  // Asynchronous reset drives out to 0 promptly (allow 0-1 delta)
  a_async_clr:  assert property (@(negedge rst) ##[0:1] (out == 4'h0));

  // Increment when enabled (ignore cycles under reset and across reset boundary)
  a_inc:        assert property (@cb disable iff (!rst)
                                 $past(rst) && $past(en) |-> (out == $past(out) + 4'h1));

  // Hold when not enabled
  a_hold:       assert property (@cb disable iff (!rst)
                                 $past(rst) && !$past(en) |-> (out == $past(out)));

  // If value changed across clocks (not due to reset), enable must have been 1 and change is +1 (mod 16)
  a_change_on_en_only:
                 assert property (@cb disable iff (!rst)
                                   $past(rst) && rst && (out != $past(out))
                                   |-> ($past(en) && (out == $past(out) + 4'h1)));

  // Coverage
  c_reset_pulse: cover property (@cb $fell(rst) ##[1:$] $rose(rst));
  c_rollover:    cover property (@cb disable iff (!rst)
                                 $past(rst) && $past(en) && ($past(out)==4'hF) && (out==4'h0));
  c_hold_seen:   cover property (@cb disable iff (!rst)
                                 $past(rst) && !$past(en) && (out == $past(out)));

endmodule

// Bind into DUT
bind counter_4bit counter_4bit_sva sva_i(.clk(clk), .rst(rst), .en(en), .out(out));
// SVA for SyncCounter
module SyncCounter_sva(input clk, input rst, input [3:0] count, input [3:0] leds);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_rst_nxt0:   assert property (rst |=> count == 4'd0);
  a_rst_hold:   assert property ((rst && $past(rst)) |-> (count == 4'd0 && $stable(count)));

  // LEDs mirror count
  a_leds_mirror: assert property (leds == count);

  // No X/Z when not in reset
  a_no_x:       assert property (disable iff (rst) !$isunknown({count, leds}));

  // +1 modulo-16 on every non-reset cycle
  a_inc_mod16:  assert property (disable iff (rst) count == (($past(count) + 4'd1) & 4'hF));

  // Explicit wrap check
  a_wrap:       assert property (disable iff (rst) ($past(count) == 4'hF) |-> (count == 4'h0));

  // Coverage
  c_deassert:   cover property (rst ##1 !rst);
  c_wrap:       cover property (disable iff (rst) $past(count)==4'hF && count==4'h0);
  c_full_cycle: cover property (disable iff (rst)
                    count==4'h0 ##1 count==4'h1 ##1 count==4'h2 ##1 count==4'h3 ##1
                    count==4'h4 ##1 count==4'h5 ##1 count==4'h6 ##1 count==4'h7 ##1
                    count==4'h8 ##1 count==4'h9 ##1 count==4'hA ##1 count==4'hB ##1
                    count==4'hC ##1 count==4'hD ##1 count==4'hE ##1 count==4'hF ##1 count==4'h0);
endmodule

// Bind into DUT
bind SyncCounter SyncCounter_sva sva_i(.clk(clk), .rst(rst), .count(count), .leds(leds));
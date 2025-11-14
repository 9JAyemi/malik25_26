// SVA for mod_add16
// Bind this file to the DUT

module mod_add16_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic [3:0]  out
);

  // Output must be known
  a_known_out: assert property (@(posedge clk) !$isunknown(out));

  // While reset is high, output is held at 0 on every clk
  a_reset_hold: assert property (@(posedge clk) rst |-> (out == 4'h0));

  // On the clk edge where reset rises, output is 0 (reset dominates)
  a_reset_rise_zero: assert property (@(posedge clk) $rose(rst) |-> (out == 4'h0));

  // Functional check: registered modulo-16 sum of prior-cycle inputs
  a_modsum: assert property (@(posedge clk) disable iff (rst)
                             out == (($past(a) + $past(b)) & 4'hF));

  // Coverage: exercise reset
  c_async_reset_seen: cover property (@(posedge rst) 1);
  c_sync_reset_seen:  cover property (@(posedge clk) $rose(rst));

  // Coverage: no-wrap and wrap-around cases of the sum
  c_no_wrap: cover property (@(posedge clk) disable iff (rst)
                             (($past(a)+$past(b)) < 16) &&
                             (out == (($past(a)+$past(b)) & 4'hF)));

  c_wrap:    cover property (@(posedge clk) disable iff (rst)
                             (($past(a)+$past(b)) >= 16) &&
                             (out == (($past(a)+$past(b)) - 16)));

endmodule

bind mod_add16 mod_add16_sva sva_i (.*);
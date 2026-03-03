// SVA for frequency_divider
module frequency_divider_sva #(
  parameter int unsigned DIV = 10
) (
  input  logic        clk_in,
  input  logic        rst,
  input  logic        clk_out,
  input  logic [31:0] count
);

  // Sanity on parameter
  initial assert (DIV >= 1) else $error("DIV must be >= 1");

  default clocking cb @(posedge clk_in); endclocking

  // Asynchronous reset clears immediately (same time step)
  a_async_reset_clears: assert property (@(posedge rst) ##0 (count==0 && clk_out==0));

  // While reset is asserted, outputs are held at zero on each clk_in edge
  a_hold_zero_during_rst: assert property (@(posedge clk_in) rst |-> (count==0 && clk_out==0));

  // No X/Z when not in reset
  a_no_unknowns: assert property (disable iff (rst) !$isunknown({clk_out, count}));

  // Count is always within range when not in reset
  a_count_in_range: assert property (disable iff (rst) ($unsigned(count) < DIV));

  // Next-state behavior (non-wrap): increment count, clk_out stable
  a_next_if_not_wrap: assert property (
    disable iff (rst)
    (count != (DIV-1)) |=> (count == $past(count)+1 && !$changed(clk_out))
  );

  // Next-state behavior (wrap): reset count to 0 and toggle clk_out
  a_next_if_wrap: assert property (
    disable iff (rst)
    (count == (DIV-1)) |=> (count == 0 && $changed(clk_out))
  );

  // clk_out may toggle only on wrap
  a_toggle_only_on_wrap: assert property (
    disable iff (rst)
    $changed(clk_out) |-> ($past(count) == (DIV-1))
  );

  // Exact half-period: consecutive clk_out changes are exactly DIV cycles apart
  a_exact_halfperiod: assert property (
    disable iff (rst)
    $changed(clk_out) |-> (!$changed(clk_out))[* (DIV-1)] ##1 $changed(clk_out)
  );

  // Coverage
  c_wrap:          cover property (disable iff (rst) (count == (DIV-1)) |=> (count == 0));
  c_toggle_r2f:    cover property (disable iff (rst) $rose(clk_out) ##DIV $fell(clk_out));
  c_toggle_f2r:    cover property (disable iff (rst) $fell(clk_out) ##DIV $rose(clk_out));
  c_two_periods:   cover property (disable iff (rst) $changed(clk_out) ##DIV $changed(clk_out) ##DIV $changed(clk_out));

endmodule

// Bind into DUT
bind frequency_divider frequency_divider_sva #(.DIV(div))
  frequency_divider_sva_i (.clk_in(clk_in), .rst(rst), .clk_out(clk_out), .count(count));
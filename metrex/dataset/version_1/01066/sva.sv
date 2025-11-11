// SVA for WDT — concise, high-quality checks and coverage
module WDT_sva #(parameter int unsigned t = 10) (
  input logic clk, rst, wdt
);
  default clocking cb @ (posedge clk); endclocking

  // 1) Counter reset behavior (synchronous reset)
  property p_rst_clears_next;
    rst |=> counter == 32'd0;
  endproperty
  assert property (p_rst_clears_next);

  property p_rst_holds_zero;
    (rst && $past(rst)) |-> counter == 32'd0;
  endproperty
  assert property (p_rst_holds_zero);

  // 2) Counter increments by 1 when not in reset (wrap allowed)
  property p_inc_when_running;
    disable iff (rst) counter == $past(counter) + 32'd1;
  endproperty
  assert property (p_inc_when_running);

  // 3) Functional definition: wdt reflects (counter >= t)
  assert property (wdt == (counter >= t));

  // 4) Reset effect on wdt (for t>0, deassert next cycle; for t==0, always 1)
  generate
    if (t > 0) begin
      assert property (rst |=> !wdt);
    end else begin
      assert property (wdt);
    end
  endgenerate

  // 5) WDT must assert exactly when threshold is crossed
  //    (with #2 and #3 this guarantees the latency from reset release)
  property p_wdt_rises_at_threshold;
    disable iff (rst) ($past(counter) == t-1) |-> wdt;
  endproperty
  assert property (p_wdt_rises_at_threshold);

  // Coverage
  cover property ($fell(rst));                   // saw reset release
  cover property ($fell(rst) ##1 counter == 32'd1); // first post-reset increment
  cover property ($fell(rst) ##[0:$] $rose(wdt));   // eventually timed out
endmodule

// Bind into the DUT (accesses internal 'counter' symbol)
bind WDT WDT_sva #(.t(t)) wdt_sva_bind (.*);
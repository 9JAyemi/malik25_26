// SVA for glitch_filter. Bind this module to the DUT.
// Focus: reset behavior, shift-chain integrity, update gating, liveness, X checks, and coverage.

module glitch_filter_sva #(parameter int n=8, t=2) ();
  // Assertions see DUT internals via bind (delay_line, sig_out_reg)
  // default clock
  default clocking cb @(posedge clk); endclocking

  // --------------------
  // Reset behavior
  // --------------------
  // All pipeline stages and output clear during reset
  generate
    for (genvar k = 0; k < t; k++) begin : g_rst_clear
      assert property (reset |-> delay_line[k] == '0)
        else $error("delay_line[%0d] not 0 during reset", k);
    end
  endgenerate
  assert property (reset |-> sig_out == '0)
    else $error("sig_out not 0 during reset");

  // --------------------
  // Shift-chain integrity
  // --------------------
  // After reset release (one-cycle grace), stages shift correctly
  assert property (disable iff (reset || $past(reset)) delay_line[0] == $past(sig_in))
    else $error("delay_line[0] != past(sig_in)");
  generate
    for (genvar j = 1; j < t; j++) begin : g_shift
      assert property (disable iff (reset || $past(reset)) delay_line[j] == $past(delay_line[j-1]))
        else $error("delay_line[%0d] != past(delay_line[%0d])", j, j-1);
    end
  endgenerate

  // --------------------
  // Output update gating
  // --------------------
  // Update only when current equals t-1 delayed value; otherwise hold prior value
  assert property (disable iff (reset || $past(reset))
                   (sig_in == delay_line[t-1]) |=> sig_out == $past(sig_in))
    else $error("sig_out not updated to past(sig_in) on match");
  assert property (disable iff (reset || $past(reset))
                   (sig_in != delay_line[t-1]) |=> sig_out == $past(sig_out))
    else $error("sig_out did not hold on mismatch");

  // Output change implies correct cause and value
  assert property (disable iff (reset || $past(reset))
                   $changed(sig_out) |-> ($past(sig_in == delay_line[t-1]) && (sig_out == $past(sig_in))))
    else $error("sig_out changed without valid match or wrong value");

  // --------------------
  // Liveness: stable input for t cycles must update output next cycle
  // --------------------
  assert property (disable iff (reset || $past(reset))
                   $stable(sig_in)[*t] |=> sig_out == $past(sig_in))
    else $error("Stable input for t cycles did not propagate to output");

  // --------------------
  // Structural/consistency checks
  // --------------------
  // Output wire mirrors internal reg
  assert property (sig_out == sig_out_reg)
    else $error("sig_out != sig_out_reg");
  // No X/Z propagation (outside reset)
  assert property (disable iff (reset) !$isunknown(sig_out))
    else $error("sig_out is X/Z");
  generate
    for (genvar x = 0; x < t; x++) begin : g_no_x
      assert property (disable iff (reset) !$isunknown(delay_line[x]))
        else $error("delay_line[%0d] is X/Z", x);
    end
  endgenerate

  // --------------------
  // Functional coverage
  // --------------------
  // Reset then deassert
  cover property (reset ##1 !reset);
  // Match path: equality followed by output change
  cover property (disable iff (reset) (sig_in == delay_line[t-1]) ##1 $changed(sig_out));
  // Mismatch path: inequality followed by no output change
  cover property (disable iff (reset) (sig_in != delay_line[t-1]) ##1 !$changed(sig_out));
  // Stable input t cycles leading to update
  cover property (disable iff (reset) $stable(sig_in)[*t] ##1 (sig_out == $past(sig_in)));
  // Any output toggle
  cover property (disable iff (reset) $changed(sig_out));

endmodule

// Bind into all glitch_filter instances with their parameters
bind glitch_filter glitch_filter_sva #(.n(n), .t(t)) u_glitch_filter_sva();
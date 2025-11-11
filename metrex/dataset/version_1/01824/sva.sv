// SVA for altera_reset_synchronizer
// Place inside the module or bind to it. Focuses on essential behavior and coverage.
`ifndef SYNTHESIS
// Basic sanity on parameters
initial assert (DEPTH >= 2)
  else $error("altera_reset_synchronizer: DEPTH (%0d) must be >= 2", DEPTH);

// Default clock for synchronous checks
default clocking cb @(posedge clk); endclocking

// Helper to gate $past-based assertions at time 0
bit past_valid;
initial past_valid = 0;
always @(posedge clk) past_valid <= 1'b1;

generate
if (ASYNC_RESET) begin : SVA_ASYNC
  // Immediate async assertion: out must go high immediately on posedge reset_in
  property p_async_assert_immediate;
    @(posedge reset_in) reset_out;
  endproperty
  assert property (p_async_assert_immediate)
    else $error("ASYNC: reset_out must assert immediately on posedge reset_in");

  // While reset_in is high, at every clk edge chain and out must be 1s
  assert property (reset_in |-> (altera_reset_synchronizer_int_chain == {DEPTH{1'b1}} && altera_reset_synchronizer_int_chain_out && reset_out))
    else $error("ASYNC: chain/out must be all-ones while reset_in=1");

  // No async deassert: on negedge reset_in, out must remain 1 immediately
  property p_no_async_deassert;
    @(negedge reset_in) reset_out;
  endproperty
  assert property (p_no_async_deassert)
    else $error("ASYNC: reset_out must not deassert asynchronously");

  // Synchronous shift behavior when not in async reset (previous cycle low and now low)
  // Next-state relations checked one cycle later
  if (DEPTH > 1) begin : SVA_SHIFT
    genvar i;
    for (i = 0; i < DEPTH-1; i++) begin : SH
      assert property (disable iff (!past_valid) (!$past(reset_in) && !reset_in) |-> (altera_reset_synchronizer_int_chain[i] == $past(altera_reset_synchronizer_int_chain[i+1])))
        else $error("ASYNC: chain shift mismatch at bit %0d", i);
    end
  end
  assert property (disable iff (!past_valid) (!$past(reset_in) && !reset_in) |-> (altera_reset_synchronizer_int_chain[DEPTH-1] == 1'b0))
    else $error("ASYNC: MSB must be 0 when shifting after reset deassert");
  assert property (disable iff (!past_valid) (!$past(reset_in) && !reset_in) |-> (altera_reset_synchronizer_int_chain_out == $past(altera_reset_synchronizer_int_chain[0]) && reset_out == altera_reset_synchronizer_int_chain_out))
    else $error("ASYNC: output flop/assign mismatch during shift");

  // Deassert timing: if reset_in stays low for DEPTH+1 clocks after a fall,
  // reset_out must stay 1 for DEPTH clocks, then deassert on the next
  assert property (disable iff (reset_in)
                   $fell(reset_in) && (!reset_in [* (DEPTH+1)])
                   |-> (reset_out[*DEPTH] ##1 !reset_out))
    else $error("ASYNC: reset_out deassert timing mismatch");

  // Monotonic while input low: at clk edges, reset_out cannot rise while reset_in=0
  assert property ((!reset_in) |-> !$rose(reset_out))
    else $error("ASYNC: reset_out rose while reset_in low");

  // Coverage
  cover property ($rose(reset_in));                                           // async assert seen
  cover property ($fell(reset_in) ##1 reset_out[*DEPTH] ##1 !reset_out);      // deassert sequence
end else begin : SVA_SYNC
  // Synchronous shift behavior
  if (DEPTH > 1) begin : SVA_SHIFT
    genvar i;
    for (i = 0; i < DEPTH-1; i++) begin : SH
      assert property (disable iff (!past_valid) altera_reset_synchronizer_int_chain[i] == $past(altera_reset_synchronizer_int_chain[i+1]))
        else $error("SYNC: chain shift mismatch at bit %0d", i);
    end
  end
  assert property (disable iff (!past_valid) altera_reset_synchronizer_int_chain[DEPTH-1] == $past(reset_in))
    else $error("SYNC: MSB must capture reset_in");
  assert property (disable iff (!past_valid) altera_reset_synchronizer_int_chain_out == $past(altera_reset_synchronizer_int_chain[0]))
    else $error("SYNC: output flop must capture LSB");
  assert property (reset_out == altera_reset_synchronizer_int_chain_out)
    else $error("SYNC: reset_out must equal output register");

  // No asynchronous output changes: reset_out only changes on clk edge
  property p_sync_out_changes_only_on_clk;
    @(posedge reset_in or negedge reset_in) $stable(reset_out);
  endproperty
  assert property (p_sync_out_changes_only_on_clk)
    else $error("SYNC: reset_out changed asynchronously");

  // End-to-end latency for assertion: if reset_in stays high DEPTH+1 clocks after a rise, out must be high after DEPTH+1
  assert property ($rose(reset_in) && (reset_in [* (DEPTH+1)]) |-> ##(DEPTH+1) reset_out)
    else $error("SYNC: reset_out assert latency mismatch");

  // End-to-end latency for deassertion: if reset_in stays low DEPTH+1 clocks after a fall, out must be low after DEPTH+1
  assert property ($fell(reset_in) && (!reset_in [* (DEPTH+1)]) |-> ##(DEPTH+1) !reset_out)
    else $error("SYNC: reset_out deassert latency mismatch");

  // Coverage
  cover property ($rose(reset_in) ##(DEPTH+1) reset_out);
  cover property ($fell(reset_in) ##(DEPTH+1) !reset_out);
end
endgenerate
`endif
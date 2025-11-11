// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic [3:0]  reset,
  input logic [3:0]  enable,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals at sampling
  assert property (!$isunknown({reset, enable, count})))
    else $error("X/Z detected on reset/enable/count");

  // Single concise next-state functional check (reset has priority)
  // Next count equals:
  //   0                    if reset==4'hF
  //   count+1 (no wrap)    if enable==4'hF and count!=4'hF
  //   0                    if enable==4'hF and count==4'hF (wrap)
  //   hold                 otherwise
  property p_next_state;
    $past(1'b1) |->
      count ==
        ( $past(reset)==4'hF ? 4'h0 :
          ( $past(enable)==4'hF
              ? ( $past(count)==4'hF ? 4'h0 : ($past(count)+4'h1) )
              : $past(count) )
        );
  endproperty
  assert property (p_next_state)
    else $error("Next-state mismatch for count");

  // Coverage: reset behavior, increment, wrap, and hold
  cover property (reset==4'hF); // reset seen
  cover property ($past(1'b1) && $past(reset)==4'hF && count==4'h0); // reset effect
  cover property ($past(1'b1) && $past(reset)!=4'hF && $past(enable)==4'hF &&
                  count == ($past(count)+4'h1)); // increment
  cover property ($past(1'b1) && $past(reset)!=4'hF && $past(enable)==4'hF &&
                  $past(count)==4'hF && count==4'h0); // wrap-around
  cover property ($past(1'b1) && $past(reset)!=4'hF && $past(enable)!=4'hF &&
                  count==$past(count)); // hold when disabled

endmodule

// Bind example:
// bind binary_counter binary_counter_sva sva(.clk(clk), .reset(reset), .enable(enable), .count(count));
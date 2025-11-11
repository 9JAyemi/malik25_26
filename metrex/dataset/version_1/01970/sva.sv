// SVA for binary_counter. Bind this to the DUT instance.
module binary_counter_sva(input logic clk, reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Sanity: count is never X/Z at sample points
  assert property ( !$isunknown(count) )
    else $error("binary_counter: count is X/Z");

  // Reset behavior:
  // After any clock where reset is 1, count must be 0 on the next clock
  // and must remain 0 on every clock until reset deasserts.
  assert property ( reset |=> (count == 4'h0 until_with (!reset)) )
    else $error("binary_counter: reset did not clear/hold count at 0");

  // Functional next-state checks when not in reset (guard $past validity)
  // Increment by +1 when not at max
  assert property ( disable iff (reset)
                    $past(1'b1) && (count != 4'hF) |=> (count == $past(count) + 4'h1) )
    else $error("binary_counter: increment step incorrect");

  // Wrap from 0xF to 0x0
  assert property ( disable iff (reset)
                    $past(1'b1) && (count == 4'hF) |=> (count == 4'h0) )
    else $error("binary_counter: wrap-around from 0xF to 0x0 failed");

  // Optional: ensure every non-reset cycle produces a state change (covered by the two above)
  assert property ( disable iff (reset)
                    $past(1'b1) |=> (( $past(count) != 4'hF ) -> (count == $past(count)+1))
                                   and (( $past(count) == 4'hF ) -> (count == 4'h0)) )
    else $error("binary_counter: unexpected hold or transition");

  // Coverage
  // Observe a full 16-count cycle without reset
  cover property ( disable iff (reset)
                   (count==4'h0) ##1 (count==4'h1) ##1 (count==4'h2) ##1 (count==4'h3) ##1
                   (count==4'h4) ##1 (count==4'h5) ##1 (count==4'h6) ##1 (count==4'h7) ##1
                   (count==4'h8) ##1 (count==4'h9) ##1 (count==4'hA) ##1 (count==4'hB) ##1
                   (count==4'hC) ##1 (count==4'hD) ##1 (count==4'hE) ##1 (count==4'hF) ##1
                   (count==4'h0) );

  // Observe wrap-around E -> F -> 0 -> 1 (no reset)
  cover property ( disable iff (reset)
                   (count==4'hE) ##1 (count==4'hF) ##1 (count==4'h0) ##1 (count==4'h1) );

  // Observe reset clears on the next clock
  cover property ( reset |=> (count==4'h0) );

  // Observe post-reset resume (0 -> 1)
  cover property ( disable iff (reset) (count==4'h0) ##1 (count==4'h1) );

endmodule

// Bind to the DUT (adjust instance pathing as needed)
bind binary_counter binary_counter_sva u_binary_counter_sva(.clk(clk), .reset(reset), .count(count));
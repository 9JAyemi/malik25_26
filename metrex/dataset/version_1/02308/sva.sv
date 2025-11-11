// SVA for counter_4bit
module counter_4bit_sva(input clk, rst, input [3:0] q);

  default clocking cb @(posedge clk); endclocking

  // past-valid to avoid first-cycle $past hazards
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // X/Z checks
  assert property ( !$isunknown(rst) );
  assert property ( past_valid |-> !$isunknown(q) );

  // Complete next-state function (spec equivalence)
  assert property ( past_valid |-> q ==
                    ( $past(rst) ? 4'h0 :
                      ($past(q)==4'hF ? 4'h0 : $past(q)+4'h1) ) );

  // No async/glitch updates: q changes only on posedge clk
  assert property (@(negedge clk) $stable(q));

  // Targeted coverage
  cover property ( past_valid && $past(rst) && q==4'h0 ); // reset took effect
  cover property ( past_valid && $past(!rst && $past(q)==4'hF) && q==4'h0 ); // rollover
  cover property ( past_valid && $past(!rst && $past(q)!=4'hF) && q==$past(q)+4'h1 ); // increment

  // Full 16-count cycle without reset
  property full_cycle_no_reset;
    disable iff (rst)
      q==4'h0 ##1 q==4'h1 ##1 q==4'h2 ##1 q==4'h3 ##1
      ##1 q==4'h4 ##1 q==4'h5 ##1 q==4'h6 ##1 q==4'h7
      ##1 q==4'h8 ##1 q==4'h9 ##1 q==4'hA ##1 q==4'hB
      ##1 q==4'hC ##1 q==4'hD ##1 q==4'hE ##1 q==4'hF ##1 q==4'h0;
  endproperty
  cover property (full_cycle_no_reset);

endmodule

bind counter_4bit counter_4bit_sva sva_u(.clk(clk), .rst(rst), .q(q));
// SVA for up_down_counter — concise, high-quality checks and coverage
// Bind this file alongside the DUT.

module up_down_counter_sva (
  input clk,
  input reset,
  input enable,
  input mode,
  input [2:0] q
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (asynchronous low reset holds q at 0 on all clock samples while low)
  assert property ( !reset |-> q == 3'd0 );

  // No X/Z on output
  assert property ( !$isunknown(q) );

  // Hold when disabled
  assert property ( reset && !enable |-> $stable(q) );

  // Up-count next state (include $past(reset) to avoid time-0 $past issues)
  assert property ( reset && $past(reset) && enable && !mode && q != 3'd7 |=> q == $past(q)+1 );
  assert property ( reset && $past(reset) && enable && !mode && q == 3'd7 |=> q == 3'd0 );

  // Down-count next state
  assert property ( reset && $past(reset) && enable &&  mode && q != 3'd0 |=> q == $past(q)-1 );
  assert property ( reset && $past(reset) && enable &&  mode && q == 3'd0 |=> q == 3'd7 );

  // Coverage
  cover property ( $fell(reset) );
  cover property ( $rose(reset) );
  cover property ( reset && enable && !mode && q == 3'd7 ##1 q == 3'd0 ); // up wrap
  cover property ( reset && enable &&  mode && q == 3'd0 ##1 q == 3'd7 ); // down wrap
  cover property ( reset && enable && !mode && q == 3'd3 ##1 q == 3'd4 ); // up step
  cover property ( reset && enable &&  mode && q == 3'd4 ##1 q == 3'd3 ); // down step
  cover property ( reset && !enable ##1 $stable(q) );                     // hold case

  // Cover all states observed while out of reset
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : cov_states
      cover property ( reset && q == i[2:0] );
    end
  endgenerate

endmodule

bind up_down_counter up_down_counter_sva sva_i (
  .clk(clk), .reset(reset), .enable(enable), .mode(mode), .q(q)
);
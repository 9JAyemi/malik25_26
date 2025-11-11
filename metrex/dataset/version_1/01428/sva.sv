// SVA checker for sync_counter
module sync_counter_sva (input logic clk, rst, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Known values on sampled edges
  assert property ( !$isunknown({rst, count}) );

  // Synchronous reset: when rst is 1 at a posedge, count is 0 that cycle
  assert property ( rst |-> count == 4'd0 );

  // Functional step: after first sampled cycle, either hold at 0 under rst,
  // or increment by exactly +1 modulo-16 when not in reset
  assert property ( $past(1'b1) |-> ( rst ? (count == 4'd0)
                                          : ((count - $past(count)) == 4'd1) ) );

  // Explicit wrap check (redundant with step, but makes intent clear)
  assert property ( $past(1'b1) && !rst && $past(!rst) && ($past(count)==4'hF) |-> (count==4'h0) );

  // Coverage: observe all 0->1,1->2,...,14->15 transitions under no reset
  generate
    genvar i;
    for (i = 0; i < 15; i++) begin : COV_INC
      cover property ( $past(1'b1) && !rst && $past(!rst) &&
                       ($past(count) == i[3:0]) ##1 (count == (i+1)[3:0]) );
    end
  endgenerate

  // Coverage: wrap 15->0 under no reset
  cover property ( $past(1'b1) && !rst && $past(!rst) &&
                   ($past(count) == 4'hF) ##1 (count == 4'h0) );

  // Coverage: synchronous reset while previously non-zero
  cover property ( $past(1'b1) && ($past(count) != 4'd0) && rst && (count == 4'd0) );

  // Coverage: a reset deassert event
  cover property ( rst ##1 !rst );

endmodule

// Bind into DUT
bind sync_counter sync_counter_sva u_sync_counter_sva (.clk(clk), .rst(rst), .count(count));
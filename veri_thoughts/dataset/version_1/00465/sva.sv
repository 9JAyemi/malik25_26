// SVA for up_counter_2bit
module up_counter_2bit_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [1:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Sanity/known checks
  ap_known:           assert property ( !$isunknown({reset, enable, count}) );

  // Asynchronous reset effect observed on each clk edge while held
  ap_reset_zero:      assert property ( reset |-> count == 2'd0 );

  // Hold when enable is low (normal operation)
  ap_hold:            assert property ( disable iff (reset)
                                        !enable |=> count == $past(count) );

  // Increment by exactly +1 mod-4 when enable is high
  ap_inc:             assert property ( disable iff (reset)
                                        enable |=> count == $past(count) + 2'd1 );

  // Any change (outside reset) must be due to enable being 1 in the prior cycle
  ap_change_requires_en:
                      assert property ( disable iff (reset)
                                        (count != $past(count) && !$past(reset)) |-> $past(enable) );

  // Coverage
  // See a full 0->1->2->3 sequence across four consecutive enabled cycles
  cp_full_count_up:   cover  property ( disable iff (reset)
                                        enable ##1 (enable && count==2'd1) [*0] ##0
                                        (count==2'd0) ##1
                                        (enable, count==2'd1) ##1
                                        (enable, count==2'd2) ##1
                                        (enable, count==2'd3) );

  // See wrap from 3 to 0 when enabled
  cp_wrap:            cover  property ( disable iff (reset)
                                        (count==2'd3 && enable) |=> (count==2'd0) );

  // See a hold when enable is low
  cp_hold:            cover  property ( disable iff (reset)
                                        (!enable) ##1 (count == $past(count)) );
endmodule

// Bind into DUT
bind up_counter_2bit up_counter_2bit_sva sva_i (.clk(clk), .reset(reset), .enable(enable), .count(count));
// SVA for Broadcast_filter
// Bind into the DUT to access internal regs
bind Broadcast_filter Broadcast_filter_sva bf_sva();

module Broadcast_filter_sva;

  // These names resolve in the bound instance's scope
  // clk/reset policy
  default clocking cb @(posedge Clk); endclocking
  default disable iff (Reset);

  // Helper
  sequence prev_rollover;
    $past(time_counter) == $past(broadcast_bucket_interval);
  endsequence

  // Optional config stability (tightens checks; relax/remove if not desired)
  assume property ( !Reset && !(time_counter == broadcast_bucket_interval)
                    |-> $stable(broadcast_bucket_interval) && $stable(broadcast_bucket_depth) );

  // Async reset drives all 0s (checked synchronously; override default disable)
  assert property (disable iff (1'b0) @(posedge Clk)
                   Reset |-> (time_counter==16'd0 && broadcast_counter==16'd0 && broadcast_drop==1'b0));

  // time_counter behavior
  assert property ( !$past(Reset) && ($past(time_counter) != $past(broadcast_bucket_interval))
                    |-> time_counter == $past(time_counter) + 16'd1 );
  assert property ( prev_rollover |-> time_counter == 16'd0 );

  // broadcast_counter behavior
  // reset on bucket rollover
  assert property ( prev_rollover |-> broadcast_counter == 16'd0 );
  // increment when ptr and not at depth, no rollover
  assert property ( !$past(Reset) &&
                    !$past(time_counter == broadcast_bucket_interval) &&
                    $past(broadcast_ptr) &&
                    ($past(broadcast_counter) != $past(broadcast_bucket_depth))
                    |-> broadcast_counter == $past(broadcast_counter) + 16'd1 );
  // hold otherwise (no rollover)
  assert property ( !$past(Reset) &&
                    !$past(time_counter == broadcast_bucket_interval) &&
                    ( !$past(broadcast_ptr) || ($past(broadcast_counter) == $past(broadcast_bucket_depth)) )
                    |-> broadcast_counter == $past(broadcast_counter) );
  // never exceed depth when depth is stable this cycle
  assert property ( $stable(broadcast_bucket_depth) |-> broadcast_counter <= broadcast_bucket_depth );

  // broadcast_drop correctness (combinational relation per-cycle)
  assert property ( broadcast_drop == (broadcast_filter_en && (broadcast_counter == broadcast_bucket_depth)) );

  // Sanity: broadcast_counter only changes by +1 or resets on rollover
  assert property ( !$past(Reset) |-> ( broadcast_counter == $past(broadcast_counter)
                                     || broadcast_counter == $past(broadcast_counter)+16'd1
                                     || $past(time_counter) == $past(broadcast_bucket_interval) ) );

  // Coverage
  cover property ( prev_rollover ##1 time_counter == 16'd0 );
  cover property ( broadcast_counter == broadcast_bucket_depth );
  cover property ( broadcast_filter_en && (broadcast_counter == broadcast_bucket_depth) && broadcast_drop );
  cover property ( broadcast_bucket_interval == 16'd0 && time_counter == 16'd0 && broadcast_counter == 16'd0 );

endmodule
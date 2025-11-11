Here is a concise, high-quality SVA bind package that fully checks the DUT behavior, including subtle load/override ordering, wraparounds, sum timing, X-safety, and provides focused coverage.

bind up_down_counter up_down_counter_sva();

module up_down_counter_sva;

  // Access bound instance signals directly
  default clocking cb @(posedge clk); endclocking

  // Guard first-cycle $past use
  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Synchronous reset values (checked on the cycle after reset is observed)
  assert property (past_valid && $past(reset) |-> (up_count==4'h0 && down_count==4'hF && count==8'h00));

  // Knownness and range
  assert property (disable iff (reset) !$isunknown({up_count,down_count,count}));
  assert property (count[7:5] == 3'b000); // sum of two 4-bit numbers is <= 30

  // Count timing: sum uses previous cycle's counters
  assert property (past_valid && $past(!reset) |-> count == $past(up_count) + $past(down_count));

  // Up mode: increment up_count (load_up is overridden), optional load_down
  assert property (past_valid && $past(!reset) && $past(up_down) |-> 
                   up_count   == (($past(up_count)==4'hF) ? 4'h0 : ($past(up_count)+1)) &&
                   down_count == ($past(load_down) ? $past(count[3:0]) : $past(down_count)));

  // Down mode: decrement down_count (load_down is overridden), optional load_up
  assert property (past_valid && $past(!reset) && !$past(up_down) |-> 
                   down_count == (($past(down_count)==4'h0) ? 4'hF : ($past(down_count)-1)) &&
                   up_count   == ($past(load_up) ? $past(count[3:0]) : $past(up_count)));

  // Corner-case/behavior coverage
  cover property (past_valid && $past(!reset) && $past(up_down) && $past(up_count)==4'hF && up_count==4'h0); // up wrap
  cover property (past_valid && $past(!reset) && !$past(up_down) && $past(down_count)==4'h0 && down_count==4'hF); // down wrap
  cover property (past_valid && $past(!reset) && $past(up_down) && $past(load_down) && 
                  down_count==$past(count[3:0])); // load_down honored in up mode
  cover property (past_valid && $past(!reset) && !$past(up_down) && $past(load_up) && 
                  up_count==$past(count[3:0])); // load_up honored in down mode
  cover property (past_valid && $past(!reset) && $past(load_up) && $past(load_down) && $past(up_down) &&
                  up_count == (($past(up_count)==4'hF)?4'h0:($past(up_count)+1)) &&
                  down_count == $past(count[3:0])); // both loads, up mode
  cover property (past_valid && $past(!reset) && $past(load_up) && $past(load_down) && !$past(up_down) &&
                  up_count == $past(count[3:0]) &&
                  down_count == (($past(down_count)==4'h0)?4'hF:($past(down_count)-1))); // both loads, down mode

endmodule
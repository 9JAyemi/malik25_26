// SVA for DelayLoop: checks functional correctness, edges, ranges, and coverage
module DelayLoop_sva #(parameter int COUNT_MAX = 100)
(
  input  logic        CLOCK,
  input  logic        Clear,
  input  logic        Timeout,
  input  logic [7:0]  count
);

  // Elaboration-time parameter checks
  initial begin
    assert (COUNT_MAX >= 0)
      else $error("COUNT_MAX must be >= 0");
    assert (COUNT_MAX < (1 << $bits(count)))
      else $error("COUNT_MAX must fit in count width (%0d bits)", $bits(count));
  end

  // Guard $past on first cycle
  logic init;
  initial init = 0;
  always @(posedge CLOCK) init <= 1'b1;

  default clocking cb @(posedge CLOCK); endclocking
  default disable iff (!init);

  // No X/Z on state/output
  assert property (!$isunknown({count, Timeout})));

  // Synchronous clear behavior (same-cycle)
  assert property (Clear |-> (count == 0 && Timeout == 0));

  // Next-state behavior when Clear was low last cycle
  // Hit COUNT_MAX -> pulse Timeout and reset count
  assert property (!$past(Clear) && $past(count) == COUNT_MAX |-> (count == 0 && Timeout == 1));

  // Otherwise -> increment and no Timeout
  assert property (!$past(Clear) && $past(count) != COUNT_MAX |-> (count == $past(count) + 1 && Timeout == 0));

  // Timeout never back-to-back when COUNT_MAX > 0
  assert property ((COUNT_MAX > 0) |-> !(Timeout && $past(Timeout)));

  // Count never exceeds COUNT_MAX
  assert property (count <= COUNT_MAX);

  // Periodicity under no Clear: after a Timeout, see COUNT_MAX zeros then a Timeout
  assert property (disable iff (Clear)
                   Timeout |-> (!Timeout && !Clear)[*COUNT_MAX] ##1 Timeout);

  // Coverage
  cover property (disable iff (Clear) (!Timeout && !Clear)[*COUNT_MAX] ##1 Timeout); // one full interval
  cover property (disable iff (Clear) Timeout ##[COUNT_MAX+1:COUNT_MAX+1] Timeout);   // consecutive pulses spaced correctly
  cover property ((!Clear && (count inside {[1:COUNT_MAX-1]})) ##1 Clear);            // clear mid-count
endmodule

// Bind into DUT
bind DelayLoop DelayLoop_sva #(.COUNT_MAX(COUNT_MAX)) DelayLoop_sva_i (.*);
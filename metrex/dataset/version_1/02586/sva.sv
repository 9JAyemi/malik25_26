// SVA checker for clock_divider_sim
module clock_divider_sim_sva #(
  parameter int DIVISOR = 2
) (
  input  logic   CLK,
  input  logic   CLOCK,
  input  integer cnt
);

  // Parameter checks
  initial begin
    assert (DIVISOR >= 2)
      else $error("clock_divider_sim: DIVISOR must be >= 2 (got %0d)", DIVISOR);
  end

  default clocking cb @(posedge CLK); endclocking

  // Constants
  localparam bit IS_EVEN = (DIVISOR % 2 == 0);
  localparam int HALF    = (DIVISOR/2);
  localparam int CEIL    = (DIVISOR - HALF);

  // Basic sanity
  a_no_x:      assert property (disable iff ($initstate) !$isunknown(CLOCK) && !$isunknown(cnt));
  a_cnt_range: assert property (disable iff ($initstate) (cnt >= 0 && cnt < DIVISOR));
  a_cnt_next:  assert property (disable iff ($initstate)
                                  cnt == (($past(cnt) == DIVISOR-1) ? 0 : $past(cnt)+1));

  // Toggle legality (when and only when allowed)
  generate if (IS_EVEN) begin : g_even
    // Toggle conditions this cycle (cause change by next sample)
    a_even_toggle_req: assert property (disable iff ($initstate)
                              ((cnt == (HALF-1)) || (cnt == (DIVISOR-1))) |=> $changed(CLOCK));
    a_even_no_spur:    assert property (disable iff ($initstate)
                              $changed(CLOCK) |-> $past((cnt == (HALF-1)) || (cnt == (DIVISOR-1))));
    // Exact spacing: HALF cycles between toggles
    a_even_spacing:    assert property (disable iff ($initstate)
                              $changed(CLOCK) |-> (!$changed(CLOCK))[* (HALF-1)] ##1 $changed(CLOCK));
    // Coverage
    c_even_half:  cover property (disable iff ($initstate) (cnt == (HALF-1)) |=> $changed(CLOCK));
    c_even_full:  cover property (disable iff ($initstate) (cnt == (DIVISOR-1)) |=> $changed(CLOCK));
    c_even_pair:  cover property (disable iff ($initstate)
                          (cnt == (HALF-1)) ##1 (cnt == (DIVISOR-1)));
  end else begin : g_odd
    // Toggle conditions this cycle (cause change by next sample)
    a_odd_toggle_req: assert property (disable iff ($initstate)
                              ((cnt == HALF) || (cnt == (DIVISOR-1))) |=> $changed(CLOCK));
    a_odd_no_spur:    assert property (disable iff ($initstate)
                              $changed(CLOCK) |-> $past((cnt == HALF) || (cnt == (DIVISOR-1))));
    // Allowed spacing: either HALF or CEIL, and alternates thereafter
    sequence gap_half; (!$changed(CLOCK))[* (HALF-1)] ##1 $changed(CLOCK); endsequence
    sequence gap_ceil; (!$changed(CLOCK))[* (CEIL-1)] ##1 $changed(CLOCK); endsequence
    a_odd_spacing_ok: assert property (disable iff ($initstate)
                              $changed(CLOCK) |-> (gap_half or gap_ceil));
    a_odd_alternate:  assert property (disable iff ($initstate)
                              $changed(CLOCK) |-> ((gap_half ##1 gap_ceil) or (gap_ceil ##1 gap_half)));
    // Coverage
    c_odd_mid:   cover property (disable iff ($initstate) (cnt == HALF) |=> $changed(CLOCK));
    c_odd_full:  cover property (disable iff ($initstate) (cnt == (DIVISOR-1)) |=> $changed(CLOCK));
    c_odd_both:  cover property (disable iff ($initstate)
                          $changed(CLOCK) ##1 (gap_half ##1 gap_ceil or gap_ceil ##1 gap_half));
  end endgenerate

  // Rollover coverage
  c_rollover: cover property (disable iff ($initstate) (cnt == DIVISOR-1) |=> (cnt == 0));

endmodule

// Bind into the DUT (example)
// bind clock_divider_sim clock_divider_sim_sva #(.DIVISOR(DIVISOR))
//   u_clock_divider_sim_sva (.* , .cnt(cnt));
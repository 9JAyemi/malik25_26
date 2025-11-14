// SVA for timer. Bind this to the DUT.
// Focus: reverse correctness, tick function, state updates, pulse shape, and coverage.

module timer_sva #(
  parameter COUNTER_WIDTH = 25,
  parameter CEILING_WIDTH = 4
)(
  input  logic                    clk_in,
  input  logic [CEILING_WIDTH-1:0] ceiling_in,
  input  logic                    tick_out,
  input  logic [COUNTER_WIDTH:0]  count,
  input  logic [ (1<<CEILING_WIDTH)-1 : 0 ] revCount,
  input  logic [COUNTER_WIDTH:0]  count_next
);

  localparam int TOP_BIT = (1<<CEILING_WIDTH) - 1;

  default clocking cb @(posedge clk_in); endclocking

  // Helper: threshold value where the selected bit first becomes 1
  function automatic logic [COUNTER_WIDTH:0] threshold(input logic [CEILING_WIDTH-1:0] c);
    logic [COUNTER_WIDTH:0] t;
    t = '0;
    t[COUNTER_WIDTH - c] = 1'b1;
    return t;
  endfunction

  // Sanity: ceiling_in must not be X/Z
  assert property (!$isunknown(ceiling_in))
    else $error("ceiling_in contains X/Z");

  // reverse() mapping is correct for all bit positions
  genvar gi;
  generate
    for (gi = 0; gi <= TOP_BIT; gi++) begin : g_rev_map
      assert property (revCount[gi] == count[COUNTER_WIDTH-gi])
        else $error("reverse mapping mismatch at bit %0d", gi);
    end
  endgenerate

  // Tick function equals selected reversed bit
  assert property (tick_out == revCount[ceiling_in])
    else $error("tick_out != revCount[ceiling_in]");

  // Next-state relation: when selected bit is 0, count increments; when 1, reset
  assert property (revCount[ceiling_in] == 1'b0 |=> count == $past(count) + 1)
    else $error("count failed to increment on non-tick cycle");

  assert property (tick_out |-> (count_next == '0))
    else $error("count_next must be 0 on tick");

  assert property (tick_out |=> (count == '0))
    else $error("count must be 0 after a tick");

  // Tick is a single-cycle pulse
  assert property (tick_out |=> !tick_out)
    else $error("tick_out must not be high for consecutive cycles");

  // Tick occurs exactly at the threshold count; and only then
  assert property (tick_out |-> (count == threshold(ceiling_in)))
    else $error("tick_out high but count != threshold");

  assert property ((count == threshold(ceiling_in)) |-> tick_out)
    else $error("count reached threshold without tick_out");

  // No tick below threshold
  assert property ((count < threshold(ceiling_in)) |-> !tick_out)
    else $error("tick_out asserted below threshold");

  // Basic coverage
  cover property ($rose(tick_out));
  // Cover a tick for each possible ceiling value
  generate
    genvar c;
    for (c = 0; c <= TOP_BIT; c++) begin : g_cov_ceiling
      cover property (tick_out && (ceiling_in == c));
    end
  endgenerate

  // Cover: ceiling change triggers an immediate tick (boundary/overshoot case)
  cover property ($changed(ceiling_in) && tick_out);

endmodule

// Bind into DUT
bind timer timer_sva #(
  .COUNTER_WIDTH(COUNTER_WIDTH),
  .CEILING_WIDTH(CEILING_WIDTH)
) timer_sva_i (
  .clk_in(clk_in),
  .ceiling_in(ceiling_in),
  .tick_out(tick_out),
  .count(count),
  .revCount(revCount),
  .count_next(count_next)
);
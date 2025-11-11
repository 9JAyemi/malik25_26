// SVA for Freq_Divider
module Freq_Divider_sva #(
  parameter int unsigned sys_clk = 50_000_000,
  parameter int unsigned clk_out = 1,
  parameter int unsigned max     = sys_clk/(2*clk_out),
  parameter int unsigned N       = (max <= 1) ? 1 : $clog2(max)
) (
  input  logic              Clk_in,
  input  logic              Clk_out,
  input  logic [N-1:0]      counter
);

  // Elaboration-time sanity
  initial begin
    if (max < 1) $fatal(1, "Freq_Divider: max must be >= 1");
  end

  // No X/Z on key state at sampling edges
  assert property (@(posedge Clk_in) !$isunknown({Clk_out, counter}));

  // Counter stays in range
  assert property (@(posedge Clk_in) counter < max);

  // Normal increment and hold output when not at terminal count
  assert property (@(posedge Clk_in)
                   disable iff ($initstate || $isunknown({counter, Clk_out}))
                   (counter != max-1) |=> (counter == $past(counter)+1 && $stable(Clk_out)));

  // Wrap and toggle exactly at terminal count
  assert property (@(posedge Clk_in)
                   disable iff ($initstate || $isunknown({counter, Clk_out}))
                   (counter == max-1) |=> (counter == {N{1'b0}} && Clk_out != $past(Clk_out)));

  // Output changes only when previous cycle was terminal count
  assert property (@(posedge Clk_in)
                   disable iff ($initstate || $isunknown({counter, Clk_out}))
                   $changed(Clk_out) |-> $past(counter) == max-1);

  // Exact toggle periodicity: next toggle occurs after exactly max cycles with no intermediate changes
  assert property (@(posedge Clk_in)
                   disable iff ($initstate || $isunknown(Clk_out))
                   $changed(Clk_out) |=> (!$changed(Clk_out))[* (max-1)] ##1 $changed(Clk_out));

  // No half-cycle glitches (coarse check)
  assert property (@(negedge Clk_in) $stable(Clk_out));

  // Coverage: observe a wrap and toggle
  cover property (@(posedge Clk_in) counter == max-1 ##1 (counter == 0 && $changed(Clk_out)));

  // Coverage: full high and low durations
  cover property (@(posedge Clk_in) $rose(Clk_out) |=> (!$changed(Clk_out))[* (max-1)] ##1 $fell(Clk_out));
  cover property (@(posedge Clk_in) $fell(Clk_out) |=> (!$changed(Clk_out))[* (max-1)] ##1 $rose(Clk_out));

endmodule

// Bind into the DUT (accesses internal 'counter')
bind Freq_Divider Freq_Divider_sva #(.sys_clk(sys_clk), .clk_out(clk_out)) freq_div_sva_i
(
  .Clk_in(Clk_in),
  .Clk_out(Clk_out),
  .counter(counter)
);
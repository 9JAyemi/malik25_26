// SVA for one_shot. Bind this checker to the DUT.
// Focused, high-quality assertions with essential coverage.

module one_shot_sva #(parameter int unsigned t = 10)
(
  input logic clk,
  input logic rst,
  input logic trig,
  input logic out,
  // internal DUT regs (accessible via bind)
  input logic [31:0] count,
  input logic pulse,
  input logic out_reg
);

  // Parameter sanity (compile/elab-time)
  initial assert (t > 0) else $error("one_shot: parameter t must be > 0");

  default clocking cb @(posedge clk); endclocking
  // Operational properties disabled during reset; reset-specific ones are separate.
  default disable iff (rst);

  // Basic equivalences and X-checks
  // out must always mirror out_reg (combinational assign) and equal pulse
  assert property (@(posedge clk) out == out_reg)
    else $error("out != out_reg");
  assert property (out == pulse)
    else $error("out != pulse");
  assert property (!$isunknown({pulse, out, out_reg, count}))
    else $error("X/Z detected on key signals (outside reset)");

  // Synchronous reset behavior (same cycle)
  assert property (@(posedge clk) rst |-> (count == 32'd0 && pulse == 1'b0 && out == 1'b0 && out_reg == 1'b0))
    else $error("Reset does not synchronously clear state");

  // Acceptance/start: when trig is high while idle, we start now with count=0 and out/pulse asserted
  assert property ( (trig && !pulse) |-> (out && pulse && count == 32'd0) )
    else $error("Start condition failed (trig&&!pulse did not start pulse with count=0)");

  // Fixed-length, non-retriggerable pulse: exactly t cycles high, then low next cycle
  assert property ( (trig && !pulse) |-> (out && pulse)[*t] ##1 (!out && !pulse) )
    else $error("Pulse length not exactly t cycles or deassertion timing incorrect");

  // Count must stay within bounds while pulsing; idle implies count=0 and out=0
  assert property ( pulse |-> (count <= t-1) )
    else $error("count exceeded t-1 while pulsing");
  assert property ( !pulse |-> (count == 32'd0 && !out) )
    else $error("Idle state not clean (count/out)");

  // Transition rules for counter and pulse
  // Guard $past usage to avoid first-cycle-after-reset issues
  assert property ( (pulse && (count < t-1) && !$past(rst,1,1'b1))
                    |-> ##1 (pulse && out && (count == $past(count,1,32'd0) + 1)) )
    else $error("count did not increment by 1 during pulse");
  assert property ( pulse && (count == t-1) |-> ##1 (!pulse && !out && count == 32'd0) )
    else $error("Pulse/Count did not terminate/reset correctly at terminal count");

  // A rising start must coincide with pulse/out rising
  assert property ( (trig && !pulse) |-> ($rose(pulse) && $rose(out)) )
    else $error("Start did not produce rising edge on pulse/out");

  // Coverage: observe key scenarios
  // 1) A normal pulse of length t completes
  cover property ( (trig && !pulse) ##1 (out && pulse)[*t] ##1 (!out && !pulse) );

  // 2) Trig held high throughout a pulse does not extend it (masked retriggers)
  cover property ( (trig && !pulse) ##1 (trig)[*t] ##1 (!out && !pulse) );

  // 3) Back-to-back pulses (re-arm after exactly t cycles low)
  cover property ( (trig && !pulse) ##[t:$] (trig && !pulse) );

endmodule

// Bind into the DUT to access internal regs
bind one_shot one_shot_sva #(.t(t)) u_one_shot_sva (
  .clk     (clk),
  .rst     (rst),
  .trig    (trig),
  .out     (out),
  .count   (count),
  .pulse   (pulse),
  .out_reg (out_reg)
);
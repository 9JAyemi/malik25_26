// SVA for adaptive_filter
// Focus: functional equivalence, reset behavior, pipeline, arithmetic/truncation coverage, X-prop
// Place inside the module or bind to the instance. Uses internal signals x, e, w_reg.

`ifndef SYNTHESIS
// Default clocking and reset controls
default clocking cb @(posedge clk); endclocking

// -------------------------------------
// Combinational relationships (always)
// -------------------------------------
assert property (@cb y == (x * w_reg)[m-1:0])
  else $error("y must equal truncated x*w_reg (m LSBs)");

assert property (@cb e == (d - y))
  else $error("e must equal d - y");

assert property (@cb w == w_reg)
  else $error("w must mirror w_reg");

// -------------------------------------
// Pipeline/registering behavior
// -------------------------------------
assert property (@cb x == $past(in))
  else $error("x must be 1-cycle registered version of in");

// -------------------------------------
// LMS weight update (uses previous-cycle values)
// -------------------------------------
assert property (@cb (!reset && $past(!reset)) |-> (w_reg == $past(w_reg) + L * $past(x) * $past(e)))
  else $error("w_reg update must follow LMS rule: w_reg' = w_reg + L*x*e (all from prev cycle)");

// -------------------------------------
// Reset behavior (async reset observed at next clk)
// -------------------------------------
assert property (@cb reset |-> (w_reg == '0 && w == '0 && y == '0 && e == d))
  else $error("During reset: w_reg/w/y must be 0 and e must equal d");

// -------------------------------------
// X/Z propagation guards (when not in reset)
// -------------------------------------
assert property (@cb !reset |-> !$isunknown({in, d, x, w_reg, y, e}))
  else $error("X/Z detected on key signals while not in reset");

// -------------------------------------
// Coverage
// -------------------------------------

// Weight update occurs
cover property (@cb !reset && $changed(w_reg));

// Error converges to zero
cover property (@cb !reset && (e == '0));

// Output truncation exercised (higher bits of x*w_reg beyond m are nonzero)
cover property (@cb !reset && (|((x * w_reg) >> m)));

// Coefficient update truncation exercised (higher bits of L*x*e beyond n are nonzero)
cover property (@cb !reset && (|((L * x * e) >> n)));

// Reset sequence and first update after deassertion
cover property (@cb $rose(reset) ##1 !reset ##1 $changed(w_reg));

`endif
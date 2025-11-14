// SVA checker bound into the DUT's scope. Focused, high-quality checks and minimal coverage.

module shift_register_sva;
  // Access DUT signals directly in bound scope: clk, d, q, register
  default clocking cb @(posedge clk); endclocking

  // Track valid past samples (avoid first/early-cycle false fires)
  bit past1, past2, past3;
  always_ff @(cb) begin
    past1 <= 1'b1;
    past2 <= past1;
    past3 <= past2;
  end

  // Only start checking after at least one sample
  default disable iff (!past1)

  // q must mirror MSB of the register
  assert property (q == register[2]);

  // Core shift behavior: on each clock, register updates to prior {register[1:0], d}
  // Only check when required past values are known
  assert property (!($isunknown($past(register)) || $isunknown($past(d)))
                   |-> register == {$past(register)[1:0], $past(d)});

  // 3-cycle pipeline relation: q equals d from 3 cycles earlier (when those past inputs are known)
  assert property (past3 && !($isunknown({$past(d,1), $past(d,2), $past(d,3)}))
                   |-> q == $past(d,3));

  // Minimal, meaningful coverage: edges on d propagate to q exactly 3 cycles later
  cover property (past3 && $rose(d) ##3 $rose(q));
  cover property (past3 && $fell(d) ##3 $fell(q));
endmodule

bind shift_register shift_register_sva sva_i();
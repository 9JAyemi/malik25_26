// SVA for shift_register_counter
// Focused, high-quality checks and coverage. Bind into the DUT.

module shift_register_counter_sva;

  // We are bound inside shift_register_counter's scope; we can see its internals.
  // clk, reset, d, select, q, shift_reg, counter exist here.

  // Track $past() validity
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset behavior (no disable so they run during reset)
  assert property (@(posedge clk) reset |-> (shift_reg == 3'b000 && counter == 2'b00))
    else $error("Reset must clear shift_reg and counter to 0");
  assert property (@(posedge clk) reset && $past(reset) |-> q == $past(q))
    else $error("q must hold its value while reset stays asserted");

  // Functional checks (disabled during reset)
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // No X/Z on key signals during normal operation
  assert property ( !$isunknown(select) && !$isunknown(d) )
    else $error("Inputs select/d must not be X/Z during operation");
  assert property ( !$isunknown(shift_reg) && !$isunknown(counter) && !$isunknown(q) )
    else $error("Internals/output must not be X/Z during operation");

  // Shift mode: select==1
  // - shift_reg shifts in d
  // - counter holds
  // - q reflects previous MSB of shift_reg (non-blocking semantics)
  assert property ( past_valid && select
                    |-> shift_reg == { $past(shift_reg[1:0]), $past(d) }
                        && counter == $past(counter)
                        && q == $past(shift_reg[2]) )
    else $error("Shift mode behavior violated");

  // Counter mode: select==0
  // - shift_reg holds
  // - counter increments modulo-4
  // - q takes previous counter LSB (width truncation on q <= counter)
  assert property ( past_valid && !select
                    |-> shift_reg == $past(shift_reg)
                        && counter == ($past(counter) + 2'b01)
                        && q == $past(counter[0]) )
    else $error("Counter mode behavior violated");

  // Simple, meaningful coverage
  cover property (past_valid && select ##1 select ##1 select);                    // 3 consecutive shift cycles
  cover property (past_valid && !select ##1 !select ##1 !select ##1 !select);     // 4 consecutive count cycles
  cover property (past_valid && select ##1 !select ##1 select);                   // shift -> count -> shift
  cover property (past_valid && !select ##1 select ##1 !select);                  // count -> shift -> count

endmodule

bind shift_register_counter shift_register_counter_sva sva_shift_register_counter();
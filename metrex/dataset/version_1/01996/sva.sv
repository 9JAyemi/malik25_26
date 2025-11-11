// SVA for shift_register (bindable)
// Focus: reset behavior, load, rotate-left, Q mapping, invariants, and coverage.

module shift_register_sva;

  // Access DUT signals directly via bind scope
  // CLK, RESET_N, LOAD, DATA_IN, Q, shift_reg

  function automatic [7:0] rotl8(input [7:0] v);
    rotl8 = {v[6:0], v[7]};
  endfunction

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RESET_N)

  // Q always mirrors LSB (check at both clk and async reset events)
  assert property (@(posedge CLK or negedge RESET_N) ##0 (Q == shift_reg[0]));

  // Asynchronous active-low reset clears state immediately
  assert property (@(negedge RESET_N) ##0 (shift_reg == 8'h00 && Q == 1'b0));

  // LOAD has priority: load DATA_IN and drive Q accordingly (same-cycle, post-NBA)
  assert property (LOAD |-> ##0 (shift_reg == DATA_IN && Q == DATA_IN[0]));

  // Rotate-left when not loading
  assert property (!LOAD |-> ##0 (shift_reg == rotl8($past(shift_reg,1,!RESET_N))
                                  && Q == $past(shift_reg[7],1,!RESET_N)));

  // After 8 consecutive rotates, word returns to original
  sequence eight_rot; !LOAD[*8]; endsequence
  assert property (eight_rot |-> ##0 (shift_reg == $past(shift_reg,8,!RESET_N)));

  // Sanity: no X/Z on state/output when out of reset
  assert property (!$isunknown({shift_reg, Q}));

  // Coverage
  cover property (@(negedge RESET_N) 1);
  cover property (LOAD |-> ##0 (shift_reg == DATA_IN && Q == DATA_IN[0]));
  cover property (!LOAD && $past(shift_reg[7],1,!RESET_N) |-> ##0 (Q == 1'b1));
  cover property (eight_rot);

endmodule

bind shift_register shift_register_sva sva();
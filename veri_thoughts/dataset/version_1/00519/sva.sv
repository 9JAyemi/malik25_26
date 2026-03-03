// SVA for RegisterAdd_6
module RegisterAdd_6_sva (
  input logic add_overflow_flag,
  input logic E,
  input logic O,
  input logic CLK,
  input logic AR,
  input logic Q_reg
);

  // Default clock/reset for sequential checks
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!AR);

  // Combinational equivalence: output must match definition at all times
  assert property (add_overflow_flag === (E & O & Q_reg));

  // Async reset: Q_reg clears immediately on AR falling and stays 0 while AR=0 (checked on clocks)
  assert property (@(negedge AR) Q_reg == 1'b0);
  assert property (@(posedge CLK) !AR |-> Q_reg == 1'b0);

  // Synchronous behavior of Q_reg
  assert property (E  |=> Q_reg == $past(O));
  assert property (!E |=> Q_reg == $past(Q_reg));

  // Output behavior w.r.t. inputs on the clock
  assert property (E && O |-> add_overflow_flag);
  assert property (!E    |-> !add_overflow_flag);

  // Coverage
  cover property (@cb $fell(AR));                    // saw async reset assert
  cover property (@cb E && !O ##1 Q_reg == 1'b0);    // load 0
  cover property (@cb E &&  O ##1 Q_reg == 1'b1);    // load 1
  cover property (@cb !E ##1 Q_reg == $past(Q_reg)); // hold
  cover property (@cb E && O && add_overflow_flag);  // overflow observed

endmodule

// Bind into DUT (accesses internal Q_reg)
bind RegisterAdd_6 RegisterAdd_6_sva sva_i (
  .add_overflow_flag(add_overflow_flag),
  .E(E),
  .O(O),
  .CLK(CLK),
  .AR(AR),
  .Q_reg(Q_reg)
);
// SVA for counter. Bind or instantiate alongside DUT.

module counter_sva (
  input logic clk,
  input logic Up,
  input logic Down,
  input logic Load,
  input logic Reset,
  input logic [2:0] Q
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (!$isunknown(Q));

  // Priority and actions (same-cycle for Reset/Load; next-state for Up/Down/hold)
  assert property (Reset |-> (Q == 3'd0));
  assert property (!Reset && Load |-> (Q == 3'd7));

  // Up has priority over Down when not Reset/Load
  assert property (!Reset && !Load && Up |=> (Q == $past(Q) + 3'd1));

  // Down only when Up is low
  assert property (!Reset && !Load && !Up && Down |=> (Q == $past(Q) - 3'd1));

  // Hold when no control
  assert property (!Reset && !Load && !Up && !Down |=> (Q == $past(Q)));

  // Coverage
  cover property (Reset |-> (Q == 3'd0));
  cover property (!Reset && Load |-> (Q == 3'd7));

  // Up normal increment and wrap
  cover property (!Reset && !Load && Up && $past(Q) != 3'd7 |=> (Q == $past(Q) + 3'd1));
  cover property (!Reset && !Load && Up && $past(Q) == 3'd7 |=> (Q == 3'd0));

  // Down normal decrement and wrap
  cover property (!Reset && !Load && !Up && Down && $past(Q) != 3'd0 |=> (Q == $past(Q) - 3'd1));
  cover property (!Reset && !Load && !Up && Down && $past(Q) == 3'd0 |=> (Q == 3'd7));

  // Simultaneous Up&Down -> Up wins
  cover property (!Reset && !Load && Up && Down |=> (Q == $past(Q) + 3'd1));

  // Idle hold
  cover property (!Reset && !Load && !Up && !Down |=> (Q == $past(Q)));

  // See each count value at least once
  cover property (Q == 3'd0);
  cover property (Q == 3'd1);
  cover property (Q == 3'd2);
  cover property (Q == 3'd3);
  cover property (Q == 3'd4);
  cover property (Q == 3'd5);
  cover property (Q == 3'd6);
  cover property (Q == 3'd7);
endmodule

// Example bind:
// bind counter counter_sva i_counter_sva (.clk(clk), .Up(Up), .Down(Down), .Load(Load), .Reset(Reset), .Q(Q));
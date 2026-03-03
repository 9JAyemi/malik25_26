// SVA for top_module and sub-blocks
module top_module_sva (
  input clk, input reset,
  input [3:0] A, input [1:0] B,
  input UP, input DOWN,
  input [3:0] shifted, input [2:0] Q,
  input [7:0] q
);

  default clocking cb @(posedge clk); endclocking

  // ---------------- Barrel shifter correctness ----------------
  assert property (disable iff ($isunknown({A,B,shifted})))
    shifted == ((B==2'b00)? A :
                (B==2'b01)? {A[2:0],A[3]} :
                (B==2'b10)? {A[1:0],A[3:2]} :
                            {A[0],A[3:1]});

  // Coverage of all shift selections
  cover property (B==2'b00);
  cover property (B==2'b01);
  cover property (B==2'b10);
  cover property (B==2'b11);

  // ---------------- Up/Down counter correctness ----------------
  // Synchronous reset behavior
  assert property (reset |=> Q==3'b000);
  cover  property (reset |=> Q==3'b000);

  // Increment, decrement, and hold behaviors
  assert property (disable iff (reset || $isunknown({UP,DOWN,Q})))
    (UP && !DOWN) |=> Q == $past(Q)+3'd1;

  assert property (disable iff (reset || $isunknown({UP,DOWN,Q})))
    (!UP && DOWN) |=> Q == $past(Q)-3'd1;

  assert property (disable iff (reset || $isunknown({UP,DOWN,Q})))
    (UP && DOWN) |=> Q == $past(Q);

  assert property (disable iff (reset || $isunknown({UP,DOWN,Q})))
    (!UP && !DOWN) |=> Q == $past(Q);

  // Wrap-around coverage
  cover property (disable iff (reset || $isunknown({UP,DOWN,Q})))
    ($past(Q)==3'd7 && UP && !DOWN) |=> (Q==3'd0);

  cover property (disable iff (reset || $isunknown({UP,DOWN,Q})))
    ($past(Q)==3'd0 && !UP && DOWN) |=> (Q==3'd7);

  // Exercise all control cases
  cover property (disable iff (reset)) (UP && !DOWN);
  cover property (disable iff (reset)) (!UP && DOWN);
  cover property (disable iff (reset)) (UP && DOWN);
  cover property (disable iff (reset)) (!UP && !DOWN);

  // ---------------- Functional module correctness ----------------
  // Exact arithmetic result
  assert property (disable iff ($isunknown({shifted,Q,q})))
    q == ({4'b0000, shifted} + {3'b000, Q});

  // Carry-out/nibble-crossing coverage
  cover property (({4'b0000, shifted} + {3'b000, Q})[7:4] != 4'b0000);

  // ---------------- Sanity: no Xs on key outputs after reset ----------------
  assert property (disable iff (reset)) !$isunknown({shifted,Q,q});

endmodule

// Bind into the DUT
bind top_module top_module_sva sva_i (
  .clk   (clk),
  .reset (reset),
  .A     (A),
  .B     (B),
  .UP    (UP),
  .DOWN  (DOWN),
  .shifted (shifted),
  .Q     (Q),
  .q     (q)
);
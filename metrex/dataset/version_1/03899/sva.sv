// SVA for and4. Bind this to the DUT.
module and4_sva (input logic A,B,C,D, X, clk, rst);

  // Default synchronous context for most properties
  default clocking cb @(posedge clk); endclocking

  // --------------------
  // Reset behavior
  // --------------------
  // Asynchronous assert: output goes 0 immediately when rst falls
  assert property (@(negedge rst) ##0 (X === 1'b0))
    else $error("and4: X not 0 immediately on negedge rst");

  // While rst is low, X must be 0 at each clock
  assert property (@(posedge clk) !rst |-> (X == 1'b0))
    else $error("and4: X not held 0 while rst=0");

  // X is never X/Z during reset low
  assert property (@(posedge clk) !rst |-> !$isunknown(X))
    else $error("and4: X unknown during reset");

  // --------------------
  // Functional behavior (1-cycle latency AND)
  // --------------------
  // After reset is stably high, X equals previous cycle's A&B&C&D
  assert property (@(posedge clk) disable iff (!rst)
                   (!$rose(rst) && !$isunknown({A,B,C,D})) |-> (X == $past(A & B & C & D)))
    else $error("and4: X != $past(A&B&C&D)");

  // If inputs known, output must be known
  assert property (@(posedge clk) disable iff (!rst)
                   !$isunknown({A,B,C,D}) |-> !$isunknown(X))
    else $error("and4: X unknown with known inputs");

  // --------------------
  // No glitching: X only changes on posedge clk or negedge rst
  // --------------------
  assert property (@(posedge X or negedge X) ($rose(clk) || $fell(rst)))
    else $error("and4: X changed without clk edge or reset");

  // --------------------
  // Coverage
  // --------------------
  // Reset activity
  cover property (@(posedge clk) $fell(rst));
  cover property (@(posedge clk) $rose(rst));

  // Hit X==1 case and transitions
  cover property (@(posedge clk) disable iff (!rst) (A & B & C & D) ##1 (X == 1));
  cover property (@(posedge clk) disable iff (!rst) $rose(X));
  cover property (@(posedge clk) disable iff (!rst) $fell(X));

  // Each input alone controls X when the others are 1
  cover property (@(posedge clk) disable iff (!rst) (B & C & D & A) ##1 (X == 1));
  cover property (@(posedge clk) disable iff (!rst) (A & C & D & B) ##1 (X == 1));
  cover property (@(posedge clk) disable iff (!rst) (A & B & D & C) ##1 (X == 1));
  cover property (@(posedge clk) disable iff (!rst) (A & B & C & D) ##1 (X == 1));

  // Drop of each input causes X to drop next cycle when others are 1
  cover property (@(posedge clk) disable iff (!rst) (A & B & C & D) ##1 $fell(A) ##1 (X == 0));
  cover property (@(posedge clk) disable iff (!rst) (A & B & C & D) ##1 $fell(B) ##1 (X == 0));
  cover property (@(posedge clk) disable iff (!rst) (A & B & C & D) ##1 $fell(C) ##1 (X == 0));
  cover property (@(posedge clk) disable iff (!rst) (A & B & C & D) ##1 $fell(D) ##1 (X == 0));

endmodule

bind and4 and4_sva and4_sva_i (.A(A),.B(B),.C(C),.D(D),.X(X),.clk(clk),.rst(rst));
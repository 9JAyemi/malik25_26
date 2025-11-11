// SVA for the provided design
// Concise checkers with high-signal/value coverage, using bind

// ---------------- comparator_2bit ----------------
module comparator_2bit_sva
  (input [1:0] A, B,
   input       equal, greater);

  // Functional correctness and mutual exclusion
  assert property (@(A or B or equal or greater)
                   !$isunknown({A,B}) |->
                   (equal == (A==B)) && (greater == (A>B)) && !(equal && greater));

  // Output sanity (no X/Z when inputs known)
  assert property (@(A or B or equal or greater)
                   !$isunknown({A,B}) |->
                   !$isunknown({equal,greater}));

  // Coverage: exercise =, >, <
  cover property (@(A or B) (A==B));
  cover property (@(A or B) (A>B));
  cover property (@(A or B) (A<B));

endmodule

bind comparator_2bit comparator_2bit_sva u_comparator_2bit_sva (.*);

// ---------------- and_nor ----------------
module and_nor_sva
  (input a, b, output y);

  // Functional correctness
  assert property (@(a or b or y)
                   !$isunknown({a,b}) |->
                   y == ~(a | b));

  // Output sanity (no X/Z when inputs known)
  assert property (@(a or b or y)
                   !$isunknown({a,b}) |->
                   !$isunknown(y));

  // Coverage: all 4 input minterms
  cover property (@(a or b) (a==0 && b==0 && y==1));
  cover property (@(a or b) (a==0 && b==1 && y==0));
  cover property (@(a or b) (a==1 && b==0 && y==0));
  cover property (@(a or b) (a==1 && b==1 && y==0));

endmodule

bind and_nor and_nor_sva u_and_nor_sva (.*);

// ---------------- greater_than ----------------
module greater_than_sva
  (input clk, reset,
   input [7:0] A, B,
   input       result);

  default clocking cb @(posedge clk); endclocking

  // Reset clears state and output
  assert property (reset |-> (result_reg == 4'b0 && and_out_reg == 1'b0 && result == 1'b0));

  // Combinational relations used internally
  assert property (!reset |-> and_out == ~(comp_out[3][1] | and_out_reg));
  assert property (!reset |-> or_gate == (comp_out[3][0] || and_out_reg));

  // State update only when not coming from reset
  assert property (!reset && !$past(reset) |-> and_out_reg == $past(and_out));
  assert property (!reset && !$past(reset) |-> result_reg == { $past(result_reg[2:0]), $past(or_gate) });

  // Output = 3-cycle delayed or_gate (pipeline latency)
  assert property (!reset && $past(!reset,3) |-> result == $past(or_gate,3));

  // Independence from upper slices: outputs depend only on low 2b and history
  assert property ($stable({and_out_reg, A[1:0], B[1:0]}) && $changed({A[7:2],B[7:2]})
                   |-> $stable({and_out, or_gate}));

  // Output sanity
  assert property (!reset |-> !$isunknown({result, and_out, or_gate, and_out_reg}));

  // Coverage: drive low-slice comparator through <,=,>
  cover property (!reset ##1 (comp_out[3][0]==1'b1));                 // equal on low slice
  cover property (!reset ##1 (comp_out[3][1]==1'b1));                 // greater on low slice
  cover property (!reset ##1 (comp_out[3][0]==1'b0 && comp_out[3][1]==1'b0)); // less on low slice

  // Coverage: pipeline propagation observed at output
  cover property (!reset ##1 !reset ##1 !reset ##1 (result == $past(or_gate,3)));

  // Coverage: result toggles
  cover property (!reset and $rose(result));
  cover property (!reset and $fell(result));

  // Coverage: exercise upper comparators (even though unused)
  cover property (@(posedge clk) (comp_out[0][0] || comp_out[0][1]));
  cover property (@(posedge clk) (comp_out[1][0] || comp_out[1][1]));
  cover property (@(posedge clk) (comp_out[2][0] || comp_out[2][1]));

endmodule

bind greater_than greater_than_sva u_greater_than_sva (.*);
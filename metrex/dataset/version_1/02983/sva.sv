// SVA for mux_2to1
module mux_2to1_sva (input logic A, B, S, Y);

  // Functional correctness (delta cycle after any input change)
  assert property (@(A or B or S) (S === 1'b0) |-> ##0 (Y === A))
    else $error("mux_2to1: Y must equal A when S==0");
  assert property (@(A or B or S) (S === 1'b1) |-> ##0 (Y === B))
    else $error("mux_2to1: Y must equal B when S==1");

  // No X on Y when inputs are known
  assert property (@(A or B or S) (!$isunknown({S,A,B})) |-> ##0 (!$isunknown(Y)))
    else $error("mux_2to1: Unexpected X/Z on Y when inputs are known");

  // X-propagation semantics for unknown S
  assert property (@(A or B or S) ($isunknown(S) && (A === B)) |-> ##0 (Y === A))
    else $error("mux_2to1: With S=X and A==B, Y must equal A/B");
  assert property (@(A or B or S) ($isunknown(S) && (A !== B)) |-> ##0 $isunknown(Y))
    else $error("mux_2to1: With S=X and A!=B, Y must be X");

  // Coverage
  cover property (@(A or B or S) (S === 1'b0) ##0 (Y === A));
  cover property (@(A or B or S) (S === 1'b1) ##0 (Y === B));
  cover property (@(posedge S) ##0 (Y === B));
  cover property (@(negedge S) ##0 (Y === A));
  cover property (@(A or B or S) ($isunknown(S) && (A !== B)) ##0 $isunknown(Y));

endmodule

// Bind into the DUT
bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (.*);
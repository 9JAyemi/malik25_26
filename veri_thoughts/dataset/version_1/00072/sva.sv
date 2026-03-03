// SVA checker for sky130_fd_sc_ms__nand4b
module sky130_fd_sc_ms__nand4b_sva (input logic Y, A_N, B, C, D);

  // No X/Z on any port
  assert property (@(A_N or B or C or D or Y) !$isunknown({A_N,B,C,D,Y}))
    else $error("X/Z detected on ports");

  // Functional equivalence: Y = ~(D & C & B & ~A_N) = (A_N | ~B | ~C | ~D)
  assert property (@(A_N or B or C or D or Y) Y == (A_N | ~B | ~C | ~D))
    else $error("Functional mismatch");

  // Important implications
  assert property (@(A_N or B or C or D) (!B || !C || !D) |-> (Y == 1'b1))
    else $error("Controlling-0 on B/C/D did not force Y=1");
  assert property (@(A_N or B or C or D) (B && C && D) |-> (Y == A_N))
    else $error("When B=C=D=1, Y must equal A_N");
  assert property (@(A_N or B or C or D) (Y == 1'b0) |-> (~A_N && B && C && D))
    else $error("Y=0 without required inputs");

  // Functional coverage: all minterms that determine Y
  cover property (@(A_N or B or C or D) (~A_N &&  B &&  C &&  D && (Y==1'b0))); // only-zero case
  cover property (@(A_N or B or C or D) ( A_N &&  B &&  C &&  D && (Y==1'b1)));
  cover property (@(A_N or B or C or D) (!B  &&  C &&  D && (Y==1'b1)));
  cover property (@(A_N or B or C or D) ( B  && !C &&  D && (Y==1'b1)));
  cover property (@(A_N or B or C or D) ( B  &&  C && !D && (Y==1'b1)));

  // Toggle coverage in decisive contexts
  cover property (@(posedge A_N) (B && C && D && (Y==1'b1)));
  cover property (@(negedge A_N) (B && C && D && (Y==1'b0)));

  cover property (@(posedge B) (A_N==1'b0 && C && D && (Y==1'b0)));
  cover property (@(negedge B) (A_N==1'b0 && C && D && (Y==1'b1)));

  cover property (@(posedge C) (A_N==1'b0 && B && D && (Y==1'b0)));
  cover property (@(negedge C) (A_N==1'b0 && B && D && (Y==1'b1)));

  cover property (@(posedge D) (A_N==1'b0 && B && C && (Y==1'b0)));
  cover property (@(negedge D) (A_N==1'b0 && B && C && (Y==1'b1)));

endmodule

// Bind into DUT
bind sky130_fd_sc_ms__nand4b sky130_fd_sc_ms__nand4b_sva u_sva (.*);
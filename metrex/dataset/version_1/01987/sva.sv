// SVA for sky130_fd_sc_hd__nand2
// Bind this checker to the DUT to verify functional correctness and collect coverage.

module sky130_fd_sc_hd__nand2_sva (
  input logic A,
  input logic B,
  input logic Y
);

  // Functional correctness (4-state accurate): Y must be ~(A & B)
  // Sample on any relevant edge; ##0 defers to end of timestep for combinational settle.
  assert property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                   1'b1 |-> ##0 (Y === ~(A & B)))
    else $error("NAND2 functional mismatch: Y=%b A=%b B=%b (expected ~(A&B))", Y, A, B);

  // Output should never be Z
  assert property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                   !(Y === 1'bz))
    else $error("NAND2 output is Z");

  // Truth-table coverage (including 4-state check on Y)
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                  ##0 (A===1'b0 && B===1'b0 && Y===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                  ##0 (A===1'b0 && B===1'b1 && Y===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                  ##0 (A===1'b1 && B===1'b0 && Y===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                  ##0 (A===1'b1 && B===1'b1 && Y===1'b0));

  // Output toggle coverage
  cover property (@(posedge Y) 1'b1);
  cover property (@(negedge Y) 1'b1);

  // Optional X-behavior coverage (controlling zero dominates)
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                  ##0 (A===1'b0 && B===1'bx && Y===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
                  ##0 (B===1'b0 && A===1'bx && Y===1'b1));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__nand2 sky130_fd_sc_hd__nand2_sva u_nand2_sva (.A(A), .B(B), .Y(Y));
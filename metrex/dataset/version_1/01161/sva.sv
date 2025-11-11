// SVA for sky130_fd_sc_ls__clkdlyinv3sd3
// Function: Y is the logical inversion of A (with a buffer stage). Pure combinational.

module sky130_fd_sc_ls__clkdlyinv3sd3_sva (
  input logic A,
  input logic Y
);

  // 4-state functional correctness (also holds when A is X/Z)
  assert property (@(A or Y) (Y === ~A))
    else $error("Y must be bitwise inversion of A (4-state)");

  // When input is known, output must be known and correct (no X/Z leakage)
  assert property (@(A or Y) (! $isunknown(A)) |-> (! $isunknown(Y) && (Y == ~A)))
    else $error("Known A must produce known, correct Y");

  // Any input change must immediately (##0) reflect on output and be correct
  assert property (@(A) $changed(A) |-> ##0 ($changed(Y) && (Y === ~A)))
    else $error("Y did not update to ~A on A change");

  // No spurious output toggles without input change
  assert property (@(Y) $changed(Y) |-> $changed(A))
    else $error("Y changed without A changing");

  // Edge-specific correctness (delta-cycle safe)
  assert property (@(posedge A) ##0 (Y == 1'b0))
    else $error("On A rise, Y must fall to 0");
  assert property (@(negedge A) ##0 (Y == 1'b1))
    else $error("On A fall, Y must rise to 1");

  // Coverage: observe both A edges and corresponding Y edges
  cover property (@(posedge A) ##0 (Y == 1'b0));
  cover property (@(negedge A) ##0 (Y == 1'b1));
  cover property (@(posedge Y));
  cover property (@(negedge Y));

  // Coverage: both steady valid states
  cover property (@(A or Y) (! $isunknown(A) && A==1'b0 && Y==1'b1));
  cover property (@(A or Y) (! $isunknown(A) && A==1'b1 && Y==1'b0));

endmodule

bind sky130_fd_sc_ls__clkdlyinv3sd3 sky130_fd_sc_ls__clkdlyinv3sd3_sva sva_i (.A(A), .Y(Y));
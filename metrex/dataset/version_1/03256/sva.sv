// SVA for nand2
module nand2_sva (
  input logic A,
  input logic B,
  input logic Y,
  input logic nand0_out_Y
);

  // End-to-end function: AND
  assert property (@(A or B or Y) 1'b1 |-> ##0 (Y === (A & B)));

  // Structural checks
  assert property (@(A or B or nand0_out_Y) 1'b1 |-> ##0 (nand0_out_Y === ~(A & B)));
  assert property (@(nand0_out_Y or Y)     1'b1 |-> ##0 (Y === ~nand0_out_Y));

  // Clean output when inputs are known
  assert property (@(A or B or Y) !$isunknown({A,B}) |-> ##0 !$isunknown(Y));

  // No spurious output toggles
  assert property (@(A or B or Y) $changed(Y) |-> ($changed(A) || $changed(B)));

  // Functional coverage (truth table)
  cover property (@(A or B or Y) ##0 (!A && !B && (Y === 1'b0)));
  cover property (@(A or B or Y) ##0 (!A &&  B && (Y === 1'b0)));
  cover property (@(A or B or Y) ##0 ( A && !B && (Y === 1'b0)));
  cover property (@(A or B or Y) ##0 ( A &&  B && (Y === 1'b1)));

  // Toggle coverage
  cover property (@(A or B or Y) $rose(Y));
  cover property (@(A or B or Y) $fell(Y));

endmodule

bind nand2 nand2_sva u_nand2_sva (.A(A), .B(B), .Y(Y), .nand0_out_Y(nand0_out_Y));
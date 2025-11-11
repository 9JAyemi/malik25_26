// SVA for sky130_fd_sc_hdll__nor3b
module sky130_fd_sc_hdll__nor3b_sva
  (input logic A, B, C_N, Y);

  // Functional equivalence for known inputs
  property p_func_eq;
    @(A or B or C_N or Y)
      (!$isunknown({A,B,C_N})) |-> ##0 (Y === (C_N & ~A & ~B));
  endproperty
  assert property (p_func_eq)
    else $error("nor3b func mismatch: Y != C_N & ~A & ~B");

  // Output known when inputs known
  property p_no_x_on_y;
    @(A or B or C_N or Y)
      (!$isunknown({A,B,C_N})) |-> ##0 (!$isunknown(Y));
  endproperty
  assert property (p_no_x_on_y)
    else $error("nor3b X-prop: Y unknown with known inputs");

  // One-sided safety implications
  assert property (@(A or B or C_N or Y) (Y === 1'b1) |-> ##0 (!A && !B && C_N))
    else $error("nor3b: Y==1 without A==0,B==0,C_N==1");
  assert property (@(A or B or C_N or Y) (A === 1'b1) |-> ##0 (Y === 1'b0))
    else $error("nor3b: A==1 but Y!=0");
  assert property (@(A or B or C_N or Y) (B === 1'b1) |-> ##0 (Y === 1'b0))
    else $error("nor3b: B==1 but Y!=0");
  assert property (@(A or B or C_N or Y) (C_N === 1'b0) |-> ##0 (Y === 1'b0))
    else $error("nor3b: C_N==0 but Y!=0");

  // Full truth-table coverage (8 combos)
  cover property (@(A or B or C_N or Y) (A==0 && B==0 && C_N==1) ##0 (Y==1));
  cover property (@(A or B or C_N or Y) (A==0 && B==0 && C_N==0) ##0 (Y==0));
  cover property (@(A or B or C_N or Y) (A==0 && B==1 && C_N==1) ##0 (Y==0));
  cover property (@(A or B or C_N or Y) (A==0 && B==1 && C_N==0) ##0 (Y==0));
  cover property (@(A or B or C_N or Y) (A==1 && B==0 && C_N==1) ##0 (Y==0));
  cover property (@(A or B or C_N or Y) (A==1 && B==0 && C_N==0) ##0 (Y==0));
  cover property (@(A or B or C_N or Y) (A==1 && B==1 && C_N==1) ##0 (Y==0));
  cover property (@(A or B or C_N or Y) (A==1 && B==1 && C_N==0) ##0 (Y==0));

endmodule

bind sky130_fd_sc_hdll__nor3b sky130_fd_sc_hdll__nor3b_sva nor3b_sva_i (.A(A), .B(B), .C_N(C_N), .Y(Y));
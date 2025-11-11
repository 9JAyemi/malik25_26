// SVA for sky130_fd_sc_hd__o21bai
// Function: Y = ~(~B1_N & (A1 | A2)) = B1_N | (~A1 & ~A2)

bind sky130_fd_sc_hd__o21bai sky130_fd_sc_hd__o21bai_sva();

module sky130_fd_sc_hd__o21bai_sva;

  // Functional equivalence (inputs known -> Y matches boolean function after delta)
  property p_y_func;
    @(A1 or A2 or B1_N)
      !$isunknown({A1,A2,B1_N}) |-> ##0 (Y == (B1_N | (~A1 & ~A2)));
  endproperty
  assert property (p_y_func);

  // Structural gate checks (source(s) known -> dest matches after delta)
  property p_not;
    @(B1_N) !$isunknown(B1_N) |-> ##0 (b == ~B1_N);
  endproperty
  assert property (p_not);

  property p_or;
    @(A1 or A2) !$isunknown({A1,A2}) |-> ##0 (or0_out == (A1 | A2));
  endproperty
  assert property (p_or);

  property p_nand;
    @(b or or0_out) !$isunknown({b,or0_out}) |-> ##0 (nand0_out_Y == ~(b & or0_out));
  endproperty
  assert property (p_nand);

  property p_buf;
    @(nand0_out_Y) !$isunknown(nand0_out_Y) |-> ##0 (Y == nand0_out_Y);
  endproperty
  assert property (p_buf);

  // Known inputs imply known output
  assert property (@(A1 or A2 or B1_N) !$isunknown({A1,A2,B1_N}) |-> ##0 !$isunknown(Y));

  // Truth-table coverage (all 8 input combinations with expected Y)
  cover property (@(A1 or A2 or B1_N) ##0 (A1==0 && A2==0 && B1_N==0 && Y==1));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==0 && A2==0 && B1_N==1 && Y==1));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==0 && A2==1 && B1_N==0 && Y==0));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==0 && A2==1 && B1_N==1 && Y==1));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==1 && A2==0 && B1_N==0 && Y==0));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==1 && A2==0 && B1_N==1 && Y==1));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==1 && A2==1 && B1_N==0 && Y==0));
  cover property (@(A1 or A2 or B1_N) ##0 (A1==1 && A2==1 && B1_N==1 && Y==1));

  // Output toggle coverage
  cover property (@(Y) $rose(Y));
  cover property (@(Y) $fell(Y));

endmodule
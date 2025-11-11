// SVA for sky130_fd_sc_hdll__a21boi
// Function: Y = B1_N & ~(A1 & A2)

module a21boi_chk (
  input logic Y,
  input logic A1,
  input logic A2,
  input logic B1_N
);

  // Functional equivalence (sample after delta — ##0)
  property p_func;
    @(A1 or A2 or B1_N or Y)
      !$isunknown({A1,A2,B1_N}) |-> ##0 (Y === (B1_N & ~(A1 & A2)));
  endproperty
  assert property (p_func)
    else $error("a21boi func mismatch: Y=%0b A1=%0b A2=%0b B1_N=%0b", Y,A1,A2,B1_N);

  // Known output whenever inputs are known
  property p_known_out_when_inputs_known;
    @(A1 or A2 or B1_N or Y)
      !$isunknown({A1,A2,B1_N}) |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_known_out_when_inputs_known)
    else $error("a21boi: Y unknown with known inputs");

  // Concise sanity implications (helpful, non-redundant diagnostics)
  property p_B1N_low_forces_low;
    @(B1_N or Y) (! $isunknown(B1_N) && B1_N==1'b0) |-> ##0 (Y===1'b0);
  endproperty
  assert property (p_B1N_low_forces_low)
    else $error("a21boi: B1_N=0 must force Y=0");

  property p_A1A2_both1_forces_low;
    @(A1 or A2 or Y) (! $isunknown({A1,A2}) && (A1 & A2)) |-> ##0 (Y===1'b0);
  endproperty
  assert property (p_A1A2_both1_forces_low)
    else $error("a21boi: A1&A2=1 must force Y=0");

  // Functional coverage: all 8 input combinations with expected Y
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==0 && A2==0 && B1_N==0 ##0 (Y==0));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==0 && A2==0 && B1_N==1 ##0 (Y==1));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==0 && A2==1 && B1_N==0 ##0 (Y==0));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==0 && A2==1 && B1_N==1 ##0 (Y==1));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==1 && A2==0 && B1_N==0 ##0 (Y==0));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==1 && A2==0 && B1_N==1 ##0 (Y==1));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==1 && A2==1 && B1_N==0 ##0 (Y==0));
  cover property (@(A1 or A2 or B1_N) ! $isunknown({A1,A2,B1_N}) && A1==1 && A2==1 && B1_N==1 ##0 (Y==0));

  // Edge coverage on Y (observed under known inputs)
  cover property (@(posedge Y) ! $isunknown({A1,A2,B1_N}));
  cover property (@(negedge Y) ! $isunknown({A1,A2,B1_N}));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hdll__a21boi a21boi_chk u_a21boi_chk (.Y(Y), .A1(A1), .A2(A2), .B1_N(B1_N));
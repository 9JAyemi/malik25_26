// SVA checker for sky130_fd_sc_hd__ha (half-adder)
module sky130_fd_sc_hd__ha_sva (
  input logic A,
  input logic B,
  input logic SUM,
  input logic COUT
);
  default clocking cb @($global_clock); endclocking

  // Functional correctness when inputs are known
  assert property (!$isunknown({A,B}) |-> (! $isunknown({SUM,COUT}) && {COUT,SUM} == (A + B)));
  assert property (!$isunknown({A,B}) |-> SUM  == (A ^ B));
  assert property (!$isunknown({A,B}) |-> COUT == (A & B));

  // No spurious output activity when inputs are stable
  assert property ($stable({A,B}) |-> $stable({SUM,COUT}));

  // Truth table coverage
  cover property ({A,B}==2'b00 && {COUT,SUM}==2'b00);
  cover property ({A,B}==2'b01 && {COUT,SUM}==2'b01);
  cover property ({A,B}==2'b10 && {COUT,SUM}==2'b01);
  cover property ({A,B}==2'b11 && {COUT,SUM}==2'b10);

  // Toggle coverage with expected behavior
  cover property ($changed(A) && $stable(B) && B==0 && $changed(SUM) && !$changed(COUT));
  cover property ($changed(A) && $stable(B) && B==1 && $changed(SUM) &&  $changed(COUT));
  cover property ($changed(B) && $stable(A) && A==0 && $changed(SUM) && !$changed(COUT));
  cover property ($changed(B) && $stable(A) && A==1 && $changed(SUM) &&  $changed(COUT));
endmodule

bind sky130_fd_sc_hd__ha sky130_fd_sc_hd__ha_sva ha_chk (.A(A), .B(B), .SUM(SUM), .COUT(COUT));
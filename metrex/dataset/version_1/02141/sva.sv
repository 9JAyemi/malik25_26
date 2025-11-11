// SVA for sky130_fd_sc_ms__nor2b
module sky130_fd_sc_ms__nor2b_sva (
  input logic A,
  input logic B_N,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  // Sample on any relevant edge
  default clocking cb @ (posedge A or negedge A or posedge B_N or negedge B_N or posedge Y or negedge Y); endclocking

  // Functional relation when inputs are known
  assert property ( !$isunknown({A,B_N}) |-> (Y === ((~A) & B_N)) );

  // Dominating-zero cases and sole 1-case
  assert property ( B_N === 1'b0 |-> Y === 1'b0 );
  assert property ( A   === 1'b1 |-> Y === 1'b0 );
  assert property ( (A===1'b0 && B_N===1'b1) |-> Y===1'b1 );

  // High output implies unique input combination
  assert property ( (Y===1'b1) |-> (A===1'b0 && B_N===1'b1) );

  // X-propagation expectations
  assert property ( (A===1'b0 && $isunknown(B_N)) |-> $isunknown(Y) );
  assert property ( (B_N===1'b1 && $isunknown(A)) |-> $isunknown(Y) );

  // No high-Z on output
  assert property ( Y !== 1'bz );

  // Power/ground rails constant
  initial begin
    assert (VPWR === 1'b1);
    assert (VPB  === 1'b1);
    assert (VGND === 1'b0);
    assert (VNB  === 1'b0);
  end

  // Truth-table coverage
  cover property ( A===1'b0 && B_N===1'b0 && Y===1'b0 );
  cover property ( A===1'b0 && B_N===1'b1 && Y===1'b1 );
  cover property ( A===1'b1 && B_N===1'b0 && Y===1'b0 );
  cover property ( A===1'b1 && B_N===1'b1 && Y===1'b0 );

  // X-propagation coverage (masked and unmasked)
  cover property ( A===1'b0 && $isunknown(B_N) && $isunknown(Y) );
  cover property ( B_N===1'b1 && $isunknown(A) && $isunknown(Y) );
  cover property ( A===1'b1 && $isunknown(B_N) && Y===1'b0 );

  // Output edge coverage
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

endmodule

// Bind SVA to the DUT (connect internal supplies by name)
bind sky130_fd_sc_ms__nor2b sky130_fd_sc_ms__nor2b_sva
(
  .A(A),
  .B_N(B_N),
  .Y(Y),
  .VPWR(VPWR),
  .VGND(VGND),
  .VPB(VPB),
  .VNB(VNB)
);
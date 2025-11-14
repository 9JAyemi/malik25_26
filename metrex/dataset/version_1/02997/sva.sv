// SVA for top_module. Bind this file to the DUT.
module top_module_sva (
  input logic A, B, C, D,
  input logic [1:0] X,
  input logic Y,
  input logic Z
);

  // Trigger checks on any input change; sample after design updates (##0)
  default clocking cb @(A or B or C or D); endclocking

  function automatic logic [2:0] enc (input logic A, B, C, D);
    if (A)      enc = {1'b1, 2'd0};
    else if (B) enc = {1'b1, 2'd1};
    else if (C) enc = {1'b1, 2'd2};
    else if (D) enc = {1'b1, 2'd3};
    else        enc = 3'b000; // {Y,X}
  endfunction

  // Functional correctness (encoder and mux)
  ap_enc_map: assert property ( !$isunknown({A,B,C,D}) |-> ##0 {Y,X} == enc(A,B,C,D) );
  ap_z_mux:   assert property ( !$isunknown({A,B,C,D}) |-> ##0 Z == (A|B|C|D) );
  ap_y_z_eq:  assert property ( !$isunknown({A,B,C,D}) |-> ##0 Z == Y );

  // Known-prop: known inputs produce known outputs
  ap_known:   assert property ( !$isunknown({A,B,C,D}) |-> ##0 !$isunknown({X,Y,Z}) );

  // Coverage: none and each selected case
  cp_none:    cover  property ( !$isunknown({A,B,C,D}) && !(A|B|C|D) ##0 (X==2'd0 && !Y && !Z) );
  cp_A:       cover  property ( !$isunknown({A,B,C,D}) &&  A              ##0 (X==2'd0 &&  Y &&  Z) );
  cp_B:       cover  property ( !$isunknown({A,B,C,D}) && !A &&  B        ##0 (X==2'd1 &&  Y &&  Z) );
  cp_C:       cover  property ( !$isunknown({A,B,C,D}) && !A && !B &&  C  ##0 (X==2'd2 &&  Y &&  Z) );
  cp_D:       cover  property ( !$isunknown({A,B,C,D}) && !A && !B && !C && D ##0 (X==2'd3 && Y && Z) );

  // Coverage: priority resolution with multiple asserted inputs
  cp_AB:      cover  property ( !$isunknown({A,B,C,D}) &&  A &&  B         ##0 (X==2'd0 && Y && Z) );
  cp_BC:      cover  property ( !$isunknown({A,B,C,D}) && !A &&  B &&  C   ##0 (X==2'd1 && Y && Z) );
  cp_CD:      cover  property ( !$isunknown({A,B,C,D}) && !A && !B && C && D ##0 (X==2'd2 && Y && Z) );
  cp_ABCD:    cover  property ( !$isunknown({A,B,C,D}) &&  A &&  B && C && D ##0 (X==2'd0 && Y && Z) );

endmodule

// Bind into the DUT
bind top_module top_module_sva sva_i (.*);
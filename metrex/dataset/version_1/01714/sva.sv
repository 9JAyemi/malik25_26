// SVA for nor_gate_using_nand
// Binds into the DUT and also checks internal temps.

module nor_gate_using_nand_sva (
  input  logic a,
  input  logic b,
  input  logic out,
  input  logic temp1,
  input  logic temp2
);
  default clocking cb @(*) endclocking

  // Functional NOR check (will flag the current OR implementation)
  ap_nor_func: assert property ( !$isunknown({a,b}) |-> (! $isunknown(out) && out == ~(a|b)) )
    else $error("NOR mismatch: a=%b b=%b out=%b", a,b,out);

  // Truth table corner cases
  ap_tt00:   assert property ( (a==1'b0 && b==1'b0) |-> out==1'b1 );
  ap_tt1a:   assert property ( (a==1'b1) |-> out==1'b0 );
  ap_tt1b:   assert property ( (b==1'b1) |-> out==1'b0 );

  // Structural checks of the NAND realization
  ap_t1:     assert property ( !$isunknown(a)            |-> temp1 == ~a );
  ap_t2:     assert property ( !$isunknown(b)            |-> temp2 == ~b );
  ap_struct: assert property ( !$isunknown({temp1,temp2})|-> out   == ~(temp1 & temp2) );

  // Coverage: all input combinations and output toggles
  cp_tt00:   cover property ( a==1'b0 && b==1'b0 && out==1'b1 );
  cp_tt01:   cover property ( a==1'b0 && b==1'b1 && out==1'b0 );
  cp_tt10:   cover property ( a==1'b1 && b==1'b0 && out==1'b0 );
  cp_tt11:   cover property ( a==1'b1 && b==1'b1 && out==1'b0 );
  cp_rise:   cover property ( $rose(out) );
  cp_fall:   cover property ( $fell(out) );
endmodule

bind nor_gate_using_nand nor_gate_using_nand_sva u_nor_gate_using_nand_sva(
  .a(a), .b(b), .out(out), .temp1(temp1), .temp2(temp2)
);
// SVA for xnor_nand
// Bind-in checker; no DUT edits required.

module xnor_nand_sva (xnor_nand dut);

  // Sample on any change of inputs or output to catch activity and allow ##0 settle
  default clocking cb @(
    posedge dut.a or negedge dut.a or
    posedge dut.b or negedge dut.b or
    posedge dut.out or negedge dut.out
  ); endclocking

  // Inputs/outputs must be 2-state (helps avoid X-propagation/masked failures)
  ap_inputs_2state: assert property ( !$isunknown({dut.a, dut.b}) )
    else $error("xnor_nand: inputs contain X/Z");
  ap_out_2state:    assert property ( !$isunknown(dut.out) )
    else $error("xnor_nand: output contains X/Z");

  // Structural NAND correctness (gate-by-gate); gated to valid inputs, sampled after ##0
  ap_n1: assert property ( (!$isunknown({dut.a,dut.b})) |-> ##0
                           (dut.nand1 == ~(dut.a & dut.b)) )
    else $error("xnor_nand: nand1 != ~(a & b)");

  ap_n2: assert property ( (!$isunknown({dut.a,dut.b})) |-> ##0
                           (dut.nand2 == ~(dut.a & dut.nand1)) )
    else $error("xnor_nand: nand2 != ~(a & nand1)");

  ap_n3: assert property ( (!$isunknown({dut.a,dut.b})) |-> ##0
                           (dut.nand3 == ~(dut.b & dut.nand1)) )
    else $error("xnor_nand: nand3 != ~(b & nand1)");

  ap_n4: assert property ( (!$isunknown({dut.a,dut.b})) |-> ##0
                           (dut.out == ~(dut.nand2 & dut.nand3)) )
    else $error("xnor_nand: out != ~(nand2 & nand3)");

  // Functional equivalence: out is XNOR of a and b
  ap_func_xnor: assert property ( (!$isunknown({dut.a,dut.b})) |-> ##0
                                  (dut.out == (dut.a ~^ dut.b)) )
    else $error("xnor_nand: out != a ~^ b");

  // Coverage: all input combinations with expected output
  cp_00: cover property ( ##0 (dut.a==0 && dut.b==0 && dut.out==1) );
  cp_01: cover property ( ##0 (dut.a==0 && dut.b==1 && dut.out==0) );
  cp_10: cover property ( ##0 (dut.a==1 && dut.b==0 && dut.out==0) );
  cp_11: cover property ( ##0 (dut.a==1 && dut.b==1 && dut.out==1) );

  // Coverage: output toggles and internal node activity
  cp_out_rise: cover property ( $rose(dut.out) );
  cp_out_fall: cover property ( $fell(dut.out) );
  cp_n1_chg:   cover property ( $changed(dut.nand1) );
  cp_n2_chg:   cover property ( $changed(dut.nand2) );
  cp_n3_chg:   cover property ( $changed(dut.nand3) );

endmodule

bind xnor_nand xnor_nand_sva sva_i(.dut());
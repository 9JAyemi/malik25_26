// SVA for and_gate
module and_gate_sva (
  input logic a,
  input logic b,
  input logic out,
  input logic na,
  input logic nb,
  input logic nand_out
);
  default clocking cb @(*); endclocking

  // Functional spec: out must be a & b (allow 0-delay settle)
  a_func_and: assert property ( !$isunknown({a,b}) |-> ##0 (out === (a & b)) )
    else $error("and_gate: out must equal a & b");

  // Structural consistency with internal netlist (allow 0-delay settle)
  a_not_a:      assert property ( ##0 (na       === ~a) );
  a_not_b:      assert property ( ##0 (nb       === ~b) );
  a_nand_ab:    assert property ( ##0 (nand_out === ~(na & nb)) );
  a_out_inv:    assert property ( ##0 (out      === ~nand_out) );

  // No X/Z on internal/outputs when inputs are known
  a_no_x: assert property ( !$isunknown({a,b}) |-> ##0 !$isunknown({na,nb,nand_out,out}) );

  // Functional coverage: all input combinations and expected output
  c_00: cover property ( a==1'b0 && b==1'b0 && ##0 out==1'b0 );
  c_01: cover property ( a==1'b0 && b==1'b1 && ##0 out==1'b0 );
  c_10: cover property ( a==1'b1 && b==1'b0 && ##0 out==1'b0 );
  c_11: cover property ( a==1'b1 && b==1'b1 && ##0 out==1'b1 );
endmodule

// Bind into DUT to access internal nets as well
bind and_gate and_gate_sva sva_i (
  .a(a),
  .b(b),
  .out(out),
  .na(na),
  .nb(nb),
  .nand_out(nand_out)
);
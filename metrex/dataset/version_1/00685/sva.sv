// SVA checker for nor_gate
module nor_gate_sva(
  input logic a,
  input logic b,
  input logic out,
  input logic nand1_out,
  input logic nand2_out
);

  // Combinational correctness checks (immediate SVA)
  always_comb begin
    // Internal NAND structure correctness
    assert (nand1_out === ~a) else $error("nand1_out != ~a");
    assert (nand2_out === ~b) else $error("nand2_out != ~b");
    assert (out === ~(nand1_out & nand2_out)) else $error("out != ~(nand1_out & nand2_out)");

    // Functional spec: NOR truth (will flag if design is OR)
    assert (out === ~(a | b)) else $error("NOR mismatch: out != ~(a | b)");

    // No X/Z on out when inputs are known
    if (!$isunknown({a,b})) assert (!$isunknown(out)) else $error("out is X/Z while a,b are known");
  end

  // Coverage: exercise all input combinations and expected NOR outputs
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1 && out==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0 && out==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1 && out==0));

  // Input toggle coverage
  cover property (@(posedge a) 1);
  cover property (@(negedge a) 1);
  cover property (@(posedge b) 1);
  cover property (@(negedge b) 1);
endmodule

// Bind into all nor_gate instances (exposes internals for checking)
bind nor_gate nor_gate_sva sva_i (
  .a(a),
  .b(b),
  .out(out),
  .nand1_out(nand1_out),
  .nand2_out(nand2_out)
);
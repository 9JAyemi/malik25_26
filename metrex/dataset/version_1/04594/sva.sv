// SVA checker for nor_using_nand
module nor_using_nand_sva (
  input logic a,
  input logic b,
  input logic nand1_out,
  input logic nand2_out,
  input logic out
);

  // Disallow X/Z on inputs; with known inputs, no X/Z should appear on internal/output
  always_comb begin
    assert (! $isunknown({a,b})) else $error("Inputs X/Z: a=%b b=%b", a, b);
    if (! $isunknown({a,b})) begin
      assert (! $isunknown({nand1_out,nand2_out,out})) else
        $error("Internal/output X/Z with known inputs: n1=%b n2=%b out=%b", nand1_out, nand2_out, out);
    end
  end

  // Structural correctness of the netlist
  always_comb begin
    assert (nand1_out === ~(a & b))      else $error("nand1_out != ~(a & b)");
    assert (nand2_out === ~nand1_out)     else $error("nand2_out != ~nand1_out");
    assert (out        === ~nand2_out)    else $error("out != ~nand2_out");
  end

  // Functional spec: NOR (catches the current NAND implementation bug)
  always_comb begin
    assert (out === ~(a | b)) else $error("Spec mismatch: out != ~(a | b) (NOR)");
  end

  // Input space coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1));

  // NOR truth-table coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) ((a^b)==1 && out==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1 && out==0));
endmodule

bind nor_using_nand nor_using_nand_sva u_nor_using_nand_sva (
  .a(a),
  .b(b),
  .nand1_out(nand1_out),
  .nand2_out(nand2_out),
  .out(out)
);
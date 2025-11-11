// SVA for magnitude_comparator
module magnitude_comparator_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       out
);
  logic a_nz = |A;
  logic b_nz = |B;

  // No X/Z on inputs/outputs
  assert property (@(A or B or out) !$isunknown({A,B,out}))
    else $error("X/Z detected: A=%b B=%b out=%b", A, B, out);

  // RTL behavior (as coded): out == ((|A) > (|B))
  assert property (@(A or B or out) out === (a_nz > b_nz))
    else $error("RTL mismatch: out=%0b expected=%0b (|A=%0b |B=%0b)", out, (a_nz > b_nz), a_nz, b_nz);

  // Intended spec check (unsigned magnitude): out == (A > B)
  assert property (@(A or B or out) out === (A > B))
    else $error("Spec (A > B) violated: A=%0d B=%0d out=%0b", A, B, out);

  // Functional coverage
  cover property (@(A or B or out) (A==4'h0 && B==4'h0 && out==1'b0));
  cover property (@(A or B or out) (A!=4'h0 && B==4'h0 && out==1'b1));
  cover property (@(A or B or out) (A==4'h0 && B!=4'h0 && out==1'b0));
  cover property (@(A or B or out) (A!=4'h0 && B!=4'h0 && out==1'b0));

  // Relation space coverage (intent)
  cover property (@(A or B or out) (A >  B));
  cover property (@(A or B or out) (A <  B));
  cover property (@(A or B or out) (A == B));
endmodule

bind magnitude_comparator magnitude_comparator_sva sva_i (.A(A), .B(B), .out(out));
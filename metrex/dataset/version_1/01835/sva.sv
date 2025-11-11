// SVA for nand2
module nand2_sva (input A, B, Y);
  // Known inputs imply correct, known output
  property p_func;
    (!$isunknown({A,B})) |-> (!$isunknown(Y) && (Y === ~(A & B)));
  endproperty
  a_func: assert property (@(*) p_func) else $error("%m: nand2 functional mismatch");

  // Truth-table coverage
  for (genvar i=0; i<4; i++) begin: cov_ab
    localparam [1:0] V = i;
    cover property (@(*) ({A,B} == V));
  end
  // Output toggles
  cover property (@(*) $changed(Y));
endmodule

bind nand2 nand2_sva nand2_sva_i (.A(A), .B(B), .Y(Y));

// SVA for nand4
module nand4_sva (
  input A, B, C, D,
  input nand1_out, nand2_out,
  input Y
);
  // Known inputs imply known/correct internal nodes and output; structural and direct equivalence
  property p_func4;
    (!$isunknown({A,B,C,D})) |->
      (!$isunknown({nand1_out,nand2_out,Y})) &&
      (nand1_out === ~(A & B)) &&
      (nand2_out === ~(C & D)) &&
      (Y === ~(nand1_out & nand2_out)) &&
      (Y === ~(A & B & C & D));
  endproperty
  a_func4: assert property (@(*) p_func4) else $error("%m: nand4 functional mismatch");

  // Pure combinational: no output change without input change (zero-delay model)
  a_stable: assert property (@(*) $stable({A,B,C,D}) |-> $stable({nand1_out,nand2_out,Y}))
            else $error("%m: outputs changed without input change");

  // Full truth-table coverage on 4 inputs
  for (genvar i=0; i<16; i++) begin: cov_abcd
    localparam [3:0] V = i;
    cover property (@(*) ({A,B,C,D} == V));
  end
  // Output toggle coverage
  cover property (@(*) $changed(Y));
endmodule

bind nand4 nand4_sva nand4_sva_i (
  .A(A), .B(B), .C(C), .D(D),
  .nand1_out(nand1_out), .nand2_out(nand2_out),
  .Y(Y)
);
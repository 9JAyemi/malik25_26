// SVA checker bound to full_adder. Concise, full functional checks + coverage.
module full_adder_sva (
  input logic A, B, Cin,
  input logic Sum, Cout,
  input logic w1, w2, w3
);
  default clocking cb @(*); endclocking

  // Functional correctness and X-safety
  ap_correct:    assert property ( !$isunknown({A,B,Cin}) |-> {Cout,Sum} == (A + B + Cin) );
  ap_no_x_out:   assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout}) );

  // Structural path checks (internal signals)
  ap_w1:         assert property ( w1 == (A ^ B) );
  ap_w2:         assert property ( w2 == (w1 ^ Cin) );
  ap_w3:         assert property ( w3 == (A & B) );
  ap_sum_path:   assert property ( Sum == w2 );
  ap_cout_path:  assert property ( Cout == (w3 | (Cin & w1)) );

  // Equivalent majority form for Cout
  ap_cout_maj:   assert property ( Cout == ((A & B) | (A & Cin) | (B & Cin)) );

  // Truth-table coverage: all 8 input combos and all 4 output combos
  genvar i;
  generate for (i=0; i<8; i++) begin : g_cov_in
    cover property ( !$isunknown({A,B,Cin}) && {A,B,Cin} == i[2:0] );
  end endgenerate
  cover_sum00: cover property ( {Cout,Sum} == 2'b00 );
  cover_sum01: cover property ( {Cout,Sum} == 2'b01 );
  cover_sum10: cover property ( {Cout,Sum} == 2'b10 );
  cover_sum11: cover property ( {Cout,Sum} == 2'b11 );
endmodule

bind full_adder full_adder_sva (
  .A(A), .B(B), .Cin(Cin),
  .Sum(Sum), .Cout(Cout),
  .w1(w1), .w2(w2), .w3(w3)
);
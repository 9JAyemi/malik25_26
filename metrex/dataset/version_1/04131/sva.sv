// SVA for adder_4bit and full_adder (bindable, concise, high-value checks)

module adder_4bit_sva;
  // Bound into adder_4bit; can see A,B,S,C_out,sum,carry
  event comb_ev; always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Knownness and functional correctness
  assert property ( !$isunknown({A,B}) |-> (!$isunknown({S,C_out,sum,carry})) );
  assert property ( !$isunknown({A,B}) |-> ({C_out,S} == A + B) );

  // Ripple-chain stage checks
  assert property ( !$isunknown({A[0],B[0]})              |-> ({carry[0], sum[0]} == A[0] + B[0]) );
  assert property ( !$isunknown({A[1],B[1],carry[0]})     |-> ({carry[1], sum[1]} == A[1] + B[1] + carry[0]) );
  assert property ( !$isunknown({A[2],B[2],carry[1]})     |-> ({carry[2], sum[2]} == A[2] + B[2] + carry[1]) );
  assert property ( !$isunknown({A[3],B[3],carry[2]})     |-> ({C_out,   sum[3]} == A[3] + B[3] + carry[2]) );

  // Output mapping
  assert property ( S == sum );

  // Targeted functional coverage
  cover property ( A==4'b0000 && B==4'b0000 && S==4'b0000 && C_out==1'b0 );          // zero+zero
  cover property ( A==4'b0111 && B==4'b0001 && S==4'b1000 && C_out==1'b0 );          // long ripple
  cover property ( A==4'b1111 && B==4'b1111 && S==4'b1110 && C_out==1'b1 );          // overflow
  cover property ( (A[0]&B[0]) );                                                    // generate @bit0
  cover property ( (A[1]&B[1]) );                                                    // generate @bit1
  cover property ( (A[2]&B[2]) );                                                    // generate @bit2
  cover property ( (A[3]&B[3]) );                                                    // generate @bit3
  cover property ( ((A^B)==4'hF) && (C_out==1'b0) );                                  // full propagate (Cin=0)
endmodule

bind adder_4bit adder_4bit_sva adder_4bit_sva_i();


module full_adder_sva;
  // Bound into full_adder; can see A,B,Cin,S,Cout
  event comb_ev; always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Knownness + truth table
  assert property ( !$isunknown({A,B,Cin}) |-> (!$isunknown({S,Cout}) && {Cout,S} == A + B + Cin) );

  // Minimalistic FA coverage: generate/propagate/kill
  cover property ( A & B );                           // generate
  cover property ( (A ^ B) && Cin );                  // propagate with carry-in
  cover property ( !(A|B) &&  Cin && (Cout==1'b0) );  // kill with carry-in
endmodule

bind full_adder full_adder_sva full_adder_sva_i();
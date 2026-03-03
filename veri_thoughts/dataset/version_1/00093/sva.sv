// SVA bind module for AdderSubtractor
module AdderSubtractor_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Sub,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic [3:0] A_comp,
  input  logic [3:0] B_comp,
  input  logic [4:0] temp_sum
);

  // helper lets
  let add_sum = {1'b0, A} + {1'b0, B};
  let sub_sum = {1'b0, A} + {1'b0, (~B + 4'd1)};
  let exp_sum = Sub ? sub_sum : add_sum;

  // no X/Z on outputs when inputs are known
  assert property ( $isunknown({A,B,Sub}) || !$isunknown({S,Cout,temp_sum}) );

  // internal two's-complement generators
  assert property ( A_comp == (~A + 4'd1) );
  assert property ( B_comp == (~B + 4'd1) );

  // temp_sum correct for add/sub selection
  assert property ( temp_sum == exp_sum );

  // S is always low 4 bits of temp_sum (catch truncation/width issues)
  assert property ( S == temp_sum[3:0] );

  // Cout correctness
  assert property ( (!Sub) || (Cout == (A >= B)) );     // subtraction: Cout == no-borrow
  assert property ( ( Sub) || (Cout == temp_sum[4]) );  // addition: Cout == carry out
  // cross-check subtraction carry-out equals no-borrow
  assert property ( (!Sub) || (sub_sum[4] == (A >= B)) );

  // functional equivalence
  assert property ( S == exp_sum[3:0] );
  assert property ( (!Sub) || ((S + B) & 4'hF) == (A & 4'hF) ); // modulo-16 identity for subtract

  // concise coverage
  cover property ( Sub == 0 );                           // add mode seen
  cover property ( Sub == 1 );                           // sub mode seen
  cover property ( (Sub==0) && (temp_sum[4]==0) );       // add, no carry
  cover property ( (Sub==0) && (temp_sum[4]==1) );       // add, carry
  cover property ( (Sub==1) && (A >= B) );               // sub, no borrow
  cover property ( (Sub==1) && (A <  B) );               // sub, borrow
  cover property ( (Sub==1) && (A == B) );               // sub, equality
  cover property ( (A==4'h0) && (B==4'h0) );             // boundary: zeros
  cover property ( (A==4'hF) && (B==4'hF) && (Sub==0) ); // boundary: max+max
  cover property ( (A==4'h0) && (B==4'hF) && (Sub==1) ); // boundary: max borrow

endmodule

// Bind into DUT (accesses internal wires via port connections)
bind AdderSubtractor AdderSubtractor_sva sva (
  .A(A),
  .B(B),
  .Sub(Sub),
  .S(S),
  .Cout(Cout),
  .A_comp(A_comp),
  .B_comp(B_comp),
  .temp_sum(temp_sum)
);
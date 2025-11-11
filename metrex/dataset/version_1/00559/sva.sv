// SVA for calculator: functional equivalence, X-prop sanity, and focused coverage
module calculator_sva (
    input  signed [15:0] A,
    input  signed [15:0] B,
    input         [1:0]  op,
    input  signed [15:0] result
);

  default clocking cb @(*); endclocking
  default disable iff ($isunknown({A,B,op}));

  // Reference computations (match DUT truncation/semantics)
  let add_exp = $signed( ($signed(A) + $signed(B)) [15:0] );
  let sub_exp = $signed( ($signed(A) - $signed(B)) [15:0] );
  let mul32   = $signed(A) * $signed(B);
  let mul_exp = $signed( mul32[15:0] );
  let div_exp = $signed( $signed(A) / $signed(B) );

  // Sanity: no X/Z on result when inputs are known
  a_known: assert property (! $isunknown(result));

  // Functional correctness per operation
  a_add:  assert property (op==2'b00 |-> result == add_exp);
  a_sub:  assert property (op==2'b01 |-> result == sub_exp);
  a_mul:  assert property (op==2'b10 |-> result == mul_exp);
  a_div0: assert property (op==2'b11 && (B==0) |-> result == 16'hFFFF);
  a_div:  assert property (op==2'b11 && (B!=0) |-> result == div_exp);

  // Basic op coverage
  c_add: cover property (op==2'b00);
  c_sub: cover property (op==2'b01);
  c_mul: cover property (op==2'b10);
  c_div: cover property (op==2'b11);
  c_div0: cover property (op==2'b11 && B==0);

  // Overflow/wraparound coverage
  c_add_ovf: cover property (op==2'b00 && (A[15]==B[15]) && (result[15]!=A[15]));
  c_sub_ovf: cover property (op==2'b01 && (A[15]!=B[15]) && (result[15]!=A[15]));
  c_mul_ovf: cover property (op==2'b10 && (mul32[31:16] != {16{mul32[31]}}));

  // Division corner cases
  c_div_neg:    cover property (op==2'b11 && B!=0 && (A[15]^B[15]) && result[15]);
  c_div_exact:  cover property (op==2'b11 && B!=0 && ($signed(A) % $signed(B) == 0));
  c_div_minovf: cover property (op==2'b11 && B==-16'sd1 && A==16'sh8000);

endmodule

bind calculator calculator_sva u_calculator_sva (.*);
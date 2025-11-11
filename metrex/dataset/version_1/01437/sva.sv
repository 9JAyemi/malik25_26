// SVA for signed_mult_shift design and its submodules.
// Uses $global_clock to sample combinational behavior.

// Assertions for signed_mult
module signed_mult_sva (
  input  signed [3:0] A,
  input  signed [3:0] B,
  input  signed [7:0] out
);
  property p_mult_correct;
    @(posedge $global_clock)
      !$isunknown({A,B}) |-> (out === ($signed(A) * $signed(B)));
  endproperty
  assert property (p_mult_correct);

  // Corner-case multiplication coverage
  cover property (@(posedge $global_clock) (A == -8 && B ==  7) && out == -56);
  cover property (@(posedge $global_clock) (A ==  7 && B ==  7) && out ==  49);
  cover property (@(posedge $global_clock) (A == -8 && B == -8) && out ==  64);
endmodule

bind signed_mult signed_mult_sva u_signed_mult_sva (.A(A), .B(B), .out(out));


// Assertions for barrel_shifter
module barrel_shifter_sva (
  input [7:0]  in,
  input [3:0]  shift_amt,
  input [15:0] out
);
  // Exact semantics of the RTL: 8-bit shift, then zero-extend to 16 bits
  property p_shift_low8;
    @(posedge $global_clock)
      !$isunknown({in,shift_amt}) |-> (out[7:0]  === ((in << shift_amt) & 8'hFF));
  endproperty
  assert property (p_shift_low8);

  property p_shift_high_zero;
    @(posedge $global_clock)
      !$isunknown({in,shift_amt}) |-> (out[15:8] === 8'h00);
  endproperty
  assert property (p_shift_high_zero);

  // Coverage of extreme shift amounts
  cover property (@(posedge $global_clock) shift_amt == 0);
  cover property (@(posedge $global_clock) shift_amt == 15);
endmodule

bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (.in(in), .shift_amt(shift_amt), .out(out));


// End-to-end and internal-wire assertions for signed_mult_shift
module signed_mult_shift_sva (
  input  signed [3:0]  A,
  input  signed [3:0]  B,
  input         [3:0]  shift,
  input                dir,
  input  signed [15:0] out,
  input  signed [7:0]  mult_result,
  input         [3:0]  shift_amt
);
  let prod8  = ($signed(A) * $signed(B));        // 8-bit signed product
  let shamt  = (dir ? shift : -shift);           // 4-bit two's-complement as in RTL
  let lo8_sh = (((prod8[7:0]) << shamt) & 8'hFF);// 8-bit shift semantics

  // Internal shift_amt matches spec
  property p_shamt_internal;
    @(posedge $global_clock)
      !$isunknown({shift,dir}) |-> (shift_amt === shamt);
  endproperty
  assert property (p_shamt_internal);

  // mult_result equals product low 8 bits
  property p_mult_consistent;
    @(posedge $global_clock)
      !$isunknown({A,B}) |-> (mult_result === prod8[7:0]);
  endproperty
  assert property (p_mult_consistent);

  // End-to-end: output matches multiply-then-8b-shift behavior with zero-extend
  property p_e2e;
    @(posedge $global_clock)
      !$isunknown({A,B,shift,dir}) |-> (out[15:8] === 8'h00 && out[7:0] === lo8_sh);
  endproperty
  assert property (p_e2e);

  // Combinational stability: if inputs are stable, output is stable
  property p_stable;
    @(posedge $global_clock)
      !$isunknown({A,B,shift,dir}) && $stable({A,B,shift,dir}) |-> $stable(out);
  endproperty
  assert property (p_stable);

  // Functional coverage
  cover property (@(posedge $global_clock) dir && shift == 0);
  cover property (@(posedge $global_clock) dir && shift == 15);
  cover property (@(posedge $global_clock) !dir && shift == 1  && shift_amt == 4'hF);
  cover property (@(posedge $global_clock) !dir && shift == 4  && shift_amt == 4'hC);
  cover property (@(posedge $global_clock) (A == -8 && B == 7 && dir && shift == 1));
  cover property (@(posedge $global_clock) (A == -8 && B == -8 && !dir && shift == 8)); // -8 mod 16
endmodule

bind signed_mult_shift signed_mult_shift_sva u_signed_mult_shift_sva (
  .A(A), .B(B), .shift(shift), .dir(dir), .out(out),
  .mult_result(mult_result), .shift_amt(shift_amt)
);
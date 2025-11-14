// fp_sva.sv — SVA for fp_add/fp_sub/fp_mul (combinational, concise)

module fp_add_sva (
  input [31:0] a, b, c,
  input [31:0] a_mantissa, b_mantissa, c_mantissa,
  input [7:0]  a_exponent, b_exponent, c_exponent,
  input        a_sign, b_sign, c_sign,
  input        carry
);
  default clocking cb @(*); endclocking

  // Basic field extraction checks
  assert property (a_sign     == a[31]);
  assert property (b_sign     == b[31]);
  assert property (a_exponent == a[30:23]);
  assert property (b_exponent == b[30:23]);
  assert property (a_mantissa[31:24] == 8'h00 && a_mantissa[23] && a_mantissa[22:0] == a[22:0]);
  assert property (b_mantissa[31:24] == 8'h00 && b_mantissa[23] && b_mantissa[22:0] == b[22:0]);

  let same = (a_sign == b_sign);
  let agtb = (a_mantissa > b_mantissa);
  let maxe = (a_exponent > b_exponent) ? a_exponent : b_exponent;

  // Core add behavior
  assert property ( same |-> ( c_sign==a_sign
                             && c_exponent==a_exponent
                             && c_mantissa==(a_mantissa + b_mantissa)
                             && carry==1'b0 ) );

  assert property ( (!same && agtb) |-> ( c_sign==a_sign
                                        && c_exponent==maxe
                                        && c_mantissa==(a_mantissa - b_mantissa)
                                        && carry==1'b0 ) );

  assert property ( (!same && !agtb) |-> ( c_sign==b_sign
                                         && c_exponent==maxe
                                         && c_mantissa==(b_mantissa - a_mantissa)
                                         && carry==1'b1 ) );

  // Output assembly
  assert property ( c == {c_sign, c_exponent, c_mantissa[22:0]} );

  // Coverage
  cover property (same);
  cover property (!same && agtb);
  cover property (!same && !agtb);
  cover property (carry);
endmodule

bind fp_add fp_add_sva add_sva (.*);

module fp_sub_sva (
  input [31:0] a, b, c,
  input [31:0] a_mantissa, b_mantissa, c_mantissa,
  input [7:0]  a_exponent, b_exponent, c_exponent,
  input        a_sign, b_sign, c_sign,
  input        borrow
);
  default clocking cb @(*); endclocking

  // Basic field extraction checks
  assert property (a_sign     == a[31]);
  assert property (b_sign     == b[31]);
  assert property (a_exponent == a[30:23]);
  assert property (b_exponent == b[30:23]);
  assert property (a_mantissa[31:24] == 8'h00 && a_mantissa[23] && a_mantissa[22:0] == a[22:0]);
  assert property (b_mantissa[31:24] == 8'h00 && b_mantissa[23] && b_mantissa[22:0] == b[22:0]);

  let same = (a_sign == b_sign);
  let agtb = (a_mantissa > b_mantissa);
  let maxe = (a_exponent > b_exponent) ? a_exponent : b_exponent;

  // Core sub behavior per DUT
  assert property ( same |-> ( c_sign==a_sign
                             && c_exponent==a_exponent
                             && c_mantissa==(a_mantissa + b_mantissa)
                             && borrow==1'b0 ) );

  assert property ( (!same && agtb) |-> ( c_sign==a_sign
                                        && c_exponent==maxe
                                        && c_mantissa==(a_mantissa - b_mantissa)
                                        && borrow==1'b0 ) );

  assert property ( (!same && !agtb) |-> ( c_sign==!b_sign
                                         && c_exponent==maxe
                                         && c_mantissa==(b_mantissa - a_mantissa)
                                         && borrow==1'b1 ) );

  // Output assembly
  assert property ( c == {c_sign, c_exponent, c_mantissa[22:0]} );

  // Coverage
  cover property (same);
  cover property (!same && agtb);
  cover property (!same && !agtb);
  cover property (borrow);
endmodule

bind fp_sub fp_sub_sva sub_sva (.*);

module fp_mul_sva (
  input [31:0] a, b, c,
  input [31:0] a_mantissa, b_mantissa,
  input [7:0]  a_exponent, b_exponent, c_exponent,
  input        a_sign, b_sign, c_sign,
  input [63:0] temp
);
  default clocking cb @(*); endclocking

  // Basic field extraction checks
  assert property (a_sign     == a[31]);
  assert property (b_sign     == b[31]);
  assert property (a_exponent == a[30:23]);
  assert property (b_exponent == b[30:23]);
  assert property (a_mantissa[31:24] == 8'h00 && a_mantissa[23] && a_mantissa[22:0] == a[22:0]);
  assert property (b_mantissa[31:24] == 8'h00 && b_mantissa[23] && b_mantissa[22:0] == b[22:0]);

  // Core mul behavior
  assert property (temp == a_mantissa * b_mantissa);
  assert property (c_sign == (a_sign ^ b_sign));
  assert property (c_exponent == (a_exponent + b_exponent - 8'd127));
  assert property (c == {c_sign, c_exponent, temp[54:23]});

  // Coverage
  cover property (a_sign ^ b_sign);
  cover property (!(a_sign ^ b_sign));
  cover property (c_exponent == 8'd0);
  cover property (c_exponent == 8'hFF);
endmodule

bind fp_mul fp_mul_sva mul_sva (.*);
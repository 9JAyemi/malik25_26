// SVA checker for float_mult
// Bind this checker into the DUT and drive clk/rst_n from your TB.
module float_mult_sva (
  input logic clk,
  input logic rst_n,

  // DUT ports
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] product,

  // DUT internals (bound hierarchically)
  input logic [31:0] mantissa_a,
  input logic [31:0] mantissa_b,
  input logic [31:0] mantissa_product,
  input logic [7:0]  exponent_a,
  input logic [7:0]  exponent_b,
  input logic [7:0]  exponent_product,
  input logic        sign_a,
  input logic        sign_b,
  input logic        sign_product,
  input logic [8:0]  guard_bits,
  input logic [8:0]  round_bit,
  input logic [8:0]  sticky_bit
);

  // Reference helpers that mirror DUT algorithm and widths
  function automatic logic [31:0] f_ma(input logic [31:0] x);
    return {8'b0, 1'b1, x[22:0]};
  endfunction

  function automatic logic [31:0] f_pre_prod32(input logic [31:0] x, input logic [31:0] y);
    logic [63:0] m;
    m = x * y;               // 64b multiply
    return m[31:0];          // DUT truncates to 32b
  endfunction

  function automatic logic [7:0] f_pre_exp8(input logic [7:0] ea, input logic [7:0] eb);
    logic [7:0] t;
    t = ea + eb - 8'd127;    // 8b wrap, like DUT
    return t;
  endfunction

  let ma        = f_ma(a);
  let mb        = f_ma(b);
  let pre_prod  = f_pre_prod32(ma, mb);
  let pre_exp   = f_pre_exp8(a[30:23], b[30:23]);

  // Normalization (uses pre_prod[26])
  let norm_shift = pre_prod[26];
  let norm_mant  = norm_shift ? (pre_prod >> 1) : pre_prod;
  let norm_exp   = norm_shift ? (pre_exp + 8'd1) : pre_exp;

  // Rounding decision uses pre-normalization guard/round/sticky
  let gb     = pre_prod[25:23];
  let rb     = pre_prod[22];
  let sb     = (|pre_prod[21:0]);
  let rcond  = (gb == 3'b111) || ((gb == 3'b110) && (rb || sb));

  // Apply rounding and possible post-round normalization
  let round_mant0 = norm_mant + (rcond ? 32'd1 : 32'd0);
  let round_shift = rcond && round_mant0[26];
  let round_mant  = round_shift ? (round_mant0 >> 1) : round_mant0;
  let round_exp   = round_shift ? (norm_exp + 8'd1) : norm_exp;

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Assumptions: limit to normalized finite operands (no denorm/Inf/NaN/zero)
  assume property (a[30:23] inside {[8'd1:8'd254]});
  assume property (b[30:23] inside {[8'd1:8'd254]});

  // Field extraction and packing
  assert property (sign_a == a[31]);
  assert property (sign_b == b[31]);
  assert property (exponent_a == a[30:23]);
  assert property (exponent_b == b[30:23]);
  assert property (mantissa_a[31:24] == 8'b0 && mantissa_a[23] == 1'b1 && mantissa_a[22:0] == a[22:0]);
  assert property (mantissa_b[31:24] == 8'b0 && mantissa_b[23] == 1'b1 && mantissa_b[22:0] == b[22:0]);

  // Guard/round/sticky derived from pre_prod, upper bits zero-extended in DUT
  assert property ({6'b0, guard_bits[2:0]} == {6'b0, gb});
  assert property ({8'b0, round_bit[0]}    == {8'b0, rb});
  assert property ({8'b0, sticky_bit[0]}   == {8'b0, sb});

  // Sign/exponent/mantissa result correctness vs reference algorithm
  assert property (sign_product == (sign_a ^ sign_b));
  assert property (product[31] == sign_product);

  assert property (mantissa_product == round_mant);
  assert property (exponent_product == round_exp);

  assert property (product[30:23] == exponent_product);
  assert property (product[22:0]  == mantissa_product[22:0]);

  // Rounding condition equivalence (using DUT's guard/round/sticky regs)
  assert property ( ((guard_bits[2:0] == 3'b111) ||
                    ((guard_bits[2:0] == 3'b110) && (round_bit[0] || sticky_bit[0]))) == rcond );

  // No X/Z on outputs under valid inputs
  assert property (!$isunknown({product, sign_product, exponent_product, mantissa_product[22:0]}));

  // Functional coverage
  cover property (a[31] == b[31]);                    // same sign
  cover property (a[31] != b[31]);                    // opposite sign
  cover property (norm_shift);                        // pre-round normalization taken
  cover property (!norm_shift);                       // pre-round normalization not taken
  cover property (gb == 3'b111);                      // round by 1 via 111
  cover property ((gb == 3'b110) && (rb || sb));      // round by 1 via 110 + (rb|sb)
  cover property (rcond && round_shift);              // rounding causes carry/extra shift
  cover property (sticky_bit[0]);                     // sticky set
  cover property (!sticky_bit[0]);                    // sticky clear
  cover property ((round_exp != pre_exp));            // exponent adjusted (by norm/round)
endmodule

// Bind example (place in TB):
// bind float_mult float_mult_sva u_float_mult_sva (
//   .clk(clk), .rst_n(rst_n),
//   .a(a), .b(b), .product(product),
//   .mantissa_a(mantissa_a), .mantissa_b(mantissa_b), .mantissa_product(mantissa_product),
//   .exponent_a(exponent_a), .exponent_b(exponent_b), .exponent_product(exponent_product),
//   .sign_a(sign_a), .sign_b(sign_b), .sign_product(sign_product),
//   .guard_bits(guard_bits), .round_bit(round_bit), .sticky_bit(sticky_bit)
// );
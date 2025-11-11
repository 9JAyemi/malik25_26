// SVA checker for unsigned_multiplier
// Bind this module to the DUT instance

module unsigned_multiplier_sva (
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [15:0] p,
  // internal DUT regs (visible via bind)
  input  logic [7:0]  shift_reg,
  input  logic [3:0]  count
);

  // Create a combinational sampling event on input changes
  event ab_change;
  always @(a or b) -> ab_change;

  // Reference multiplication
  function automatic logic [15:0] ref_mul (input logic [7:0] aa, input logic [7:0] bb);
    ref_mul = aa * bb;
  endfunction

  // Core functional correctness: p must equal a*b after combinational settle
  a_mul_correct: assert property (@(ab_change) ##0 (p == ref_mul(a,b)))
    else $error("unsigned_multiplier: p != a*b (a=%0d b=%0d p=%0d exp=%0d)", a,b,p,ref_mul(a,b));

  // No X/Z on inputs/outputs after settle
  a_no_xz_io: assert property (@(ab_change) ##0 !$isunknown({a,b,p}))
    else $error("unsigned_multiplier: X/Z detected on {a,b,p}");

  // Internal algorithm completes fully in one evaluate: shift_reg -> 0, count -> 0
  a_internals_final: assert property (@(ab_change) ##0 (shift_reg == 8'h00 && count == 4'h0))
    else $error("unsigned_multiplier: internals not finalized (shift_reg=%h count=%0d)", shift_reg, count);

  // Basic corner coverage
  c_a_zero:      cover property (@(ab_change) ##0 (a == 8'h00 && p == 16'h0000));
  c_b_zero:      cover property (@(ab_change) ##0 (b == 8'h00 && p == 16'h0000));
  c_a_one:       cover property (@(ab_change) ##0 (a == 8'h01 && p == {8'h00,b}));
  c_b_one:       cover property (@(ab_change) ##0 (b == 8'h01 && p == {8'h00,a}));
  c_full_ones_b: cover property (@(ab_change) ##0 (b == 8'hFF));
  c_max_max:     cover property (@(ab_change) ##0 (a == 8'hFF && b == 8'hFF && p == 16'hFE01));
  c_high_bytes:  cover property (@(ab_change) ##0 (p[15:8] != 8'h00));
  c_multi_ones:  cover property (@(ab_change) ##0 ($countones(b) >= 2));

  // Each partial-product path (single bit set in b)
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : gen_pp_cov
      c_b_single_bit: cover property (@(ab_change) ##0 (b == (8'h1 << i) && p == (16'(a) << i)));
    end
  endgenerate

endmodule

// Bind to DUT (adjust instance/path if needed)
bind unsigned_multiplier unsigned_multiplier_sva
  sva_u (
    .a(a),
    .b(b),
    .p(p),
    .shift_reg(shift_reg),
    .count(count)
  );
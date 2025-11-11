// SVA for barrel_shift_and_separate
// Bind this checker to the DUT instance.
// Example: bind barrel_shift_and_separate barrel_shift_and_separate_sva dut_sva (.*);

module barrel_shift_and_separate_sva (
  input  logic [15:0] in,
  input  logic [3:0]  shift_amt,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo
);

  // Optional: forbid X/Z on inputs; ensures 2-state equivalence checks are meaningful
  assume property ( !$isunknown({in, shift_amt}) );

  // Outputs must not go X/Z under 2-state inputs
  assert property ( !$isunknown({out_hi, out_lo}) )
    else $error("Outputs contain X/Z");

  // Functional equivalence: outputs equal a zero-filling logical left shift
  assert property ( {out_hi, out_lo} == (in << shift_amt) )
    else $error("Shift result mismatch");

  // Zero-fill check: low bits below shift_amt are zero when shift_amt>0
  assert property ( (shift_amt != 0) |-> (({out_hi, out_lo} & ((16'h1 << shift_amt) - 1)) == 16'h0) )
    else $error("Low bits not zero-filled");

  // Idempotent case: shift by zero is pass-through
  assert property ( (shift_amt == 0) |-> ({out_hi, out_lo} == in) )
    else $error("Shift by 0 not passthrough");

  // Boundary case: max shift (15) places in[0] into MSB and zero-fills others
  assert property (
    (shift_amt == 4'd15) |-> ({out_hi, out_lo} == {in[0], 15'b0})
  ) else $error("Shift by 15 incorrect");

  // Coverage: hit all shift amounts
  genvar k;
  generate
    for (k = 0; k < 16; k++) begin : g_cov_shift
      cover property ( shift_amt == k );
      cover property ( (shift_amt == k) && ({out_hi, out_lo} == (in << k)) );
    end
  endgenerate

  // Extra corner-case coverage
  cover property ( (shift_amt == 4'd8)  && ({out_hi, out_lo} == (in << 8))  );
  cover property ( (shift_amt == 4'd15) && ({out_hi, out_lo} == (in << 15)) );

endmodule

// Suggested bind:
// bind barrel_shift_and_separate barrel_shift_and_separate_sva sva_inst (.*);
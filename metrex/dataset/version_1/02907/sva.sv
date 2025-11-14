// SVA for flt_frac_test
// Bind-in module with concise, high-value checks and coverage

module flt_frac_test_sva
(
  input  logic         clk,
  input  logic         rstn,
  input  logic [31:0]  afl,
  input  logic [47:0]  mant,
  input  logic         frac_flag
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rstn);

  // Reference computation (matches DUT intent but independent of mant reg width effects)
  let base48   = {24'b0, 1'b1, afl[22:0]};           // 48-bit zero-extended 1.f
  let left_m   = (base48 << (afl[30:23] - 8'd127));  // exp >= 128 (afl[30]==1)
  let right_m  = (base48 >> (8'd127 - afl[30:23]));  // exp <= 127 (afl[30]==0)
  let mant_exp = (afl[30]) ? left_m : right_m;
  let lsb24    = mant_exp[23:0];

  // Asynchronous reset drives frac_flag low (checked on clock boundary)
  property p_async_reset_low;
    @(posedge clk) !rstn |-> (frac_flag == 1'b0);
  endproperty
  assert property (p_async_reset_low);

  // Functional correctness: frac_flag is OR-reduction of expected lower 24 bits
  assert property (frac_flag == (|lsb24))
    else $error("frac_flag mismatch: expected %0b from |lsb24", |lsb24);

  // Internal consistency: mant equals expected 48-bit shifted value
  assert property (mant == mant_exp)
    else $error("mant mismatch");

  // Sanity: no X/Z on frac_flag when out of reset
  assert property (!$isunknown(frac_flag))
    else $error("frac_flag is X/Z");

  // Coverage: both shift directions and both zero/non-zero LSB cases
  cover property ($rose(rstn));
  cover property (afl[30]   && (|lsb24));  // left shift, non-zero frac
  cover property (afl[30]   && !(|lsb24)); // left shift, zero frac
  cover property (!afl[30]  && (|lsb24));  // right shift, non-zero frac
  cover property (!afl[30]  && !(|lsb24)); // right shift, zero frac

endmodule

bind flt_frac_test flt_frac_test_sva sva_i (.*);
// SVA for pfpu_fmul: pipeline timing, propagation, correctness, and coverage
// Bind into the DUT so we can see internals
bind pfpu_fmul pfpu_fmul_sva();

module pfpu_fmul_sva;
  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (alu_rst);

  localparam int LAT = 5; // valid_i -> valid_o latency in cycles

  function automatic bit no_rst_5();
    return !$past(alu_rst,1) && !$past(alu_rst,2) && !$past(alu_rst,3) && !$past(alu_rst,4) && !$past(alu_rst,5);
  endfunction

  // Latency: valid_o equals valid_i delayed by LAT when no resets in the window
  assert property (valid_o == ($past(valid_i,LAT) && no_rst_5()));

  // Stage-to-stage propagation (control)
  assert property (r_valid  == valid_i);
  assert property (r1_valid == $past(r_valid));
  assert property (r2_valid == $past(r1_valid));
  assert property (r3_valid == $past(r2_valid));
  assert property (r4_valid == $past(r3_valid));
  assert property (valid_o  == $past(r4_valid));

  // Stage-to-stage propagation (data and flags)
  assert property (r_zero   == ((a[30:23]==8'd0) || (b[30:23]==8'd0)));
  assert property (r1_zero  == $past(r_zero));
  assert property (r2_zero  == $past(r1_zero));
  assert property (r3_zero  == $past(r2_zero));
  assert property (r4_zero  == $past(r3_zero));

  assert property (r_sign   == (a[31]^b[31]));
  assert property (r1_sign  == $past(r_sign));
  assert property (r2_sign  == $past(r1_sign));
  assert property (r3_sign  == $past(r2_sign));
  assert property (r4_sign  == $past(r3_sign));

  assert property (r_expn   == (a[30:23] + b[30:23] - 8'd127));
  assert property (r1_expn  == $past(r_expn));
  assert property (r2_expn  == $past(r1_expn));
  assert property (r3_expn  == $past(r2_expn));
  assert property (r4_expn  == $past(r3_expn));

  assert property (r_a_mant == {1'b1, a[22:0]});
  assert property (r_b_mant == {1'b1, b[22:0]});
  assert property (r1_mant  == ($past(r_a_mant) * $past(r_b_mant)));
  assert property (r2_mant  == $past(r1_mant));
  assert property (r3_mant  == $past(r2_mant));
  assert property (r4_mant  == $past(r3_mant));

  // Output correctness when valid_o
  assert property (valid_o |-> no_rst_5());

  // Zero result: exponent is zero (sign/fraction may be X by design)
  assert property (valid_o && $past(r4_zero,1) |-> r[30:23] == 8'd0);

  // Non-zero result: normalization, sign, exponent, fraction
  assert property (valid_o && !$past(r4_zero,1) |-> r[31] == $past(r4_sign,1));
  // Product magnitude sanity (hidden-1 property)
  assert property (valid_o && !$past(r4_zero,1) |-> ($past(r4_mant,1)[47] || $past(r4_mant,1)[46]));
  // No shift case
  assert property (valid_o && !$past(r4_zero,1) && !$past(r4_mant[47],1) |->
                   r[30:23] == $past(r4_expn,1) &&
                   r[22:0]  == $past(r4_mant,1)[45:23]);
  // Shift + exponent increment case
  assert property (valid_o && !$past(r4_zero,1) &&  $past(r4_mant[47],1) |->
                   r[30:23] == ($past(r4_expn,1)+8'd1) &&
                   r[22:0]  == $past(r4_mant,1)[46:24]);

  // Tie r4_* back to original inputs (cycle-aligned to valid_o)
  assert property (valid_o && !$past(r4_zero,1) |->
                   $past(r4_sign,1) == ($past(a,LAT)[31]^$past(b,LAT)[31]));
  assert property (valid_o && !$past(r4_zero,1) |->
                   $past(r4_expn,1) == ($past(a,LAT)[30:23] + $past(b,LAT)[30:23] - 8'd127));
  assert property (valid_o && !$past(r4_zero,1) |->
                   $past(r4_mant,1) == ({1'b1, $past(a,LAT)[22:0]} * {1'b1, $past(b,LAT)[22:0]}));
  assert property (valid_o |->
                   $past(r4_zero,1) == (($past(a,LAT)[30:23]==8'd0) || ($past(b,LAT)[30:23]==8'd0)));

  // Reset behavior: all valid bits cleared when reset asserted
  assert property (@(posedge sys_clk) alu_rst |-> !r_valid && !r1_valid && !r2_valid && !r3_valid && !r4_valid && !valid_o);

  // No X on output when valid and non-zero
  assert property (valid_o && !$past(r4_zero,1) |-> !$isunknown(r));

  // Functional coverage
  cover property (valid_i ##1 !alu_rst[*LAT] ##1 valid_o);
  cover property (valid_o && $past(r4_zero,1));
  cover property (valid_o && !$past(r4_zero,1) && !$past(r4_mant[47],1));
  cover property (valid_o && !$past(r4_zero,1) &&  $past(r4_mant[47],1));
  cover property (valid_o && !$past(r4_zero,1) && ($past(a,LAT)[31]^$past(b,LAT)[31])==1'b0);
  cover property (valid_o && !$past(r4_zero,1) && ($past(a,LAT)[31]^$past(b,LAT)[31])==1'b1);
endmodule
// SVA for mul_16_32_mult
// Bind these assertions to the DUT
bind mul_16_32_mult mul_16_32_mult_sva sva_i (.*);

module mul_16_32_mult_sva
(
  input logic        CLK,
  input logic [15:0] A,
  input logic [31:0] B,
  input logic        CE,
  input logic        SCLR,
  input logic [1:0]  ZERO_DETECT,
  input logic [47:0] P,
  input logic [47:0] PCASC
);

  default clocking cb @(posedge CLK); endclocking

  // Basic sanity: outputs known
  assert property (!$isunknown({P, PCASC, ZERO_DETECT})));

  // Synchronous clear dominates and forces known reset values on next sample
  assert property (SCLR |=> (P==48'b0 && PCASC==48'b0 && ZERO_DETECT==2'b11));

  // Hold when CE=0 (no update when not cleared)
  assert property (!SCLR && !CE |=> $stable({P, PCASC, ZERO_DETECT}));

  // 48-bit MAC update for P (accumulate low 48-bits of A*B)
  assert property (!SCLR && CE |=> P == ( $past(P) + ($past(A) * $past(B)) )[47:0]);

  // 48-bit MAC update for PCASC (code reduces to same low 48-bits accumulate)
  assert property (!SCLR && CE |=> PCASC == ( $past(PCASC) + ($past(A) * $past(B)) )[47:0]);

  // P and PCASC track identically per DUT (given identical init and updates)
  assert property (P == PCASC);

  // ZERO_DETECT encoding and timing: reflects previous P and only 00 or 11
  assert property (!SCLR && CE |=> ZERO_DETECT == (($past(P)==48'b0) ? 2'b11 : 2'b00));
  assert property (ZERO_DETECT inside {2'b00, 2'b11});
  assert property (ZERO_DETECT[1] == ZERO_DETECT[0]);

  // ------------- Coverage -------------

  // See at least one synchronous clear
  cover property (SCLR);

  // See at least one MAC update that changes P
  cover property (!SCLR && CE |=> P != $past(P));

  // ZERO_DETECT asserted when previous P was zero
  cover property (!SCLR && CE && $past(P)==48'b0 |=> ZERO_DETECT==2'b11);

  // ZERO_DETECT deasserted when previous P was non-zero
  cover property (!SCLR && CE && $past(P)!=48'b0 |=> ZERO_DETECT==2'b00);

  // Observe wrap-around on addition (overflow of low 48 bits)
  cover property (!SCLR && CE |=> (( $past(P) + ($past(A)*$past(B)) )[47:0]) < $past(P));

  // Observe hold when CE=0
  cover property (!SCLR && !CE |=> $stable({P, PCASC, ZERO_DETECT}));

endmodule
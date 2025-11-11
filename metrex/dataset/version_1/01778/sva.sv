// SVA for NormaliseAdder. Bind this module to the DUT.
// Focused checks: idle passthrough, sign/frac copy, exponent/shift normalization,
// special all-zero range, and no-shift case. Includes concise per-shift asserts and coverage.

module NormaliseAdder_sva (
  input  logic        clock,
  input  logic        idle_AddState,
  input  logic [31:0] sout_AddState,
  input  logic [27:0] sum_AddState,
  input  logic        idle_NormaliseSum,
  input  logic [31:0] sout_NormaliseSum,
  input  logic [27:0] sum_NormaliseSum
);
  localparam logic put_idle = 1'b1;

  wire [7:0] s_exp = sout_AddState[30:23];

  // Make $past() well-defined from cycle 1
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  default clocking cb @(posedge clock); endclocking
  default disable iff (!past_valid);

  // 1) Idle flag propagates 1-cycle
  assert property (idle_NormaliseSum == $past(idle_AddState));

  // 2) Idle path: sout passes through, sum cleared
  assert property ($past(idle_AddState)==put_idle |-> 
                   (sout_NormaliseSum == $past(sout_AddState) &&
                    sum_NormaliseSum  == 28'd0));

  // 3) Non-idle: sign and fraction (31,22:0) copied
  assert property ($past(idle_AddState)!=put_idle |-> 
                   (sout_NormaliseSum[31]   == $past(sout_AddState[31]) &&
                    sout_NormaliseSum[22:0] == $past(sout_AddState[22:0])));

  // 4) Overflow of carry (bit 27): exponent+1, sum >> 1
  assert property ($past(idle_AddState)!=put_idle && $past(sum_AddState[27]) |-> 
                   ($unsigned(sout_NormaliseSum[30:23]) == $unsigned($past(s_exp)) + 1) &&
                   (sum_NormaliseSum == ($past(sum_AddState) >> 1)));

  // 5) Special all-zero high range [26:3]==0: exponent forced to 8'h82, sum holds
  assert property ($past(idle_AddState)!=put_idle &&
                   !$past(sum_AddState[27]) &&
                   ($past(sum_AddState[26:3]) == 24'h0) |-> 
                   (sout_NormaliseSum[30:23] == 8'h82) &&
                   (sum_NormaliseSum == $past(sum_NormaliseSum)));

  // 6) Left-shift normalization family: for k=1..23
  genvar k;
  for (k = 1; k <= 23; k++) begin : GEN_SHIFT
    localparam int IDX = 27 - k;   // bit that must be 1
    localparam int W   = k;        // width of zero slice [26:IDX]
    // Condition: not idle, no carry, high zeros [26:IDX]==0, next bit [IDX]==1
    assert property ($past(idle_AddState)!=put_idle &&
                     !$past(sum_AddState[27]) &&
                     ($past(sum_AddState[26:IDX]) == {W{1'b0}}) &&
                     $past(sum_AddState[IDX]) |-> 
                     ($unsigned($past(s_exp)) == $unsigned(sout_NormaliseSum[30:23]) + k) &&
                     (sum_NormaliseSum == ($past(sum_AddState) << k)));
    // Coverage for each shift amount k
    cover property ($past(idle_AddState)!=put_idle &&
                    !$past(sum_AddState[27]) &&
                    ($past(sum_AddState[26:IDX]) == {W{1'b0}}) &&
                    $past(sum_AddState[IDX]));
  end

  // 7) No-shift case: top bit26 already 1
  assert property ($past(idle_AddState)!=put_idle &&
                   !$past(sum_AddState[27]) &&
                   $past(sum_AddState[26]) |-> 
                   (sout_NormaliseSum[30:23] == $past(s_exp)) &&
                   (sum_NormaliseSum == $past(sum_AddState)));

  // 8) Additional coverage: idle, carry-right-shift, special all-zero, no-shift
  cover property ($past(idle_AddState)==put_idle);
  cover property ($past(idle_AddState)!=put_idle && $past(sum_AddState[27]));
  cover property ($past(idle_AddState)!=put_idle &&
                  !$past(sum_AddState[27]) &&
                  ($past(sum_AddState[26:3]) == 24'h0));
  cover property ($past(idle_AddState)!=put_idle &&
                  !$past(sum_AddState[27]) &&
                  $past(sum_AddState[26]));
endmodule

// Bind into the DUT
bind NormaliseAdder NormaliseAdder_sva sva_i (.*);
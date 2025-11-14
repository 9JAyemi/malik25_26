// SVA for barrel_shifter
// Concise, focuses on functional correctness, internal stage checks, X-prop, and coverage.
// Bind into the DUT to access internal stage regs.

module barrel_shifter_sva (
  input  logic [3:0] D,
  input  logic [1:0] A,
  input  logic [3:0] S,
  input  logic [3:0] stage1_out,
  input  logic [3:0] stage2_out,
  input  logic [3:0] stage3_out
);

  // Safe 4-bit left shift (saturates to zero for shift >= 4)
  function automatic logic [3:0] shl4 (input logic [3:0] x, input int unsigned sh);
    shl4 = (sh >= 4) ? 4'h0 : (x << sh);
  endfunction

  // Stage-by-stage functional checks (unclocked concurrent assertions)
  // Stage 1: shift by A
  assert property (
    stage1_out == shl4(D, (A==2'b00)?0 : (A==2'b01)?1 : (A==2'b10)?2 : 3)
  ) else $error("stage1_out mismatch: D=%0h A=%0b st1=%0h", D, A, stage1_out);

  // Stage 2: shift by {0,2,3,4} based on A
  assert property (
    stage2_out == shl4(stage1_out, (A==2'b00)?0 : (A==2'b01)?2 : (A==2'b10)?3 : 4)
  ) else $error("stage2_out mismatch: A=%0b st1=%0h st2=%0h", A, stage1_out, stage2_out);

  // Stage 3: shift by A
  assert property (
    stage3_out == shl4(stage2_out, (A==2'b00)?0 : (A==2'b01)?1 : (A==2'b10)?2 : 3)
  ) else $error("stage3_out mismatch: A=%0b st2=%0h st3=%0h", A, stage2_out, stage3_out);

  // Output connection and simplified end-to-end functional check
  assert property (S == stage3_out)
    else $error("S != stage3_out: S=%0h st3=%0h", S, stage3_out);

  // By algebra of the RTL, S == D when A==0; else S==0
  assert property (S == ((A==2'b00) ? D : 4'b0000))
    else $error("Functional mismatch: D=%0h A=%0b S=%0h", D, A, S);

  // No-X propagation (when inputs are known)
  assert property ( !$isunknown({A,D}) |-> !$isunknown({stage1_out,stage2_out,stage3_out,S}) )
    else $error("X/Z detected on outputs/stages with known inputs: D=%0h A=%0b", D, A);

  // Basic coverage
  cover property (A==2'b00 && S==D);           // pass-through case
  cover property (A==2'b01 && S==4'b0000);     // zeroed case
  cover property (A==2'b10 && S==4'b0000);
  cover property (A==2'b11 && S==4'b0000);
  cover property (A==2'b00 && D==4'b0000 && S==4'b0000);
  cover property (A==2'b00 && D==4'b1111 && S==4'b1111);
  cover property (A==2'b00 && D==4'b0001 && S==4'b0001);
  cover property (A==2'b00 && D==4'b1000 && S==4'b1000);

endmodule

// Bind into DUT (ports resolved in DUT scope)
bind barrel_shifter barrel_shifter_sva bsva (
  .D(D),
  .A(A),
  .S(S),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out),
  .stage3_out(stage3_out)
);
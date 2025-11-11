// SVA for subleq

module subleq_sva
(
  input logic        iClock,
  input logic        iReset,
  input logic [31:0] iInstruction,
  input logic [31:0] oIP,
  input logic [31:0] oA,
  input logic [31:0] oB,
  input logic        oJump,
  input logic [31:0] oNextIP,
  // internal state
  input logic [31:0] S, D, B, sub,
  input logic        leq
);

  default clocking cb @(posedge iClock); endclocking

  logic past_valid;
  always_ff @(posedge iClock) past_valid <= 1'b1;

  // Reset behavior
  assert property (iReset |=> (oIP==32'd0 && oA==32'd0 && oB==32'd0 && oJump==1'b0 && oNextIP==32'd0));

  // Fetch decode (zero-extend) into S/D/B next cycle
  assert property (disable iff (iReset || !past_valid)
    1'b1 |=> (S[31:8]==24'd0 && S[7:0]==$past(iInstruction[23:16]) &&
              D[31:8]==24'd0 && D[7:0]==$past(iInstruction[15:8]) &&
              B[31:8]==24'd0 && B[7:0]==$past(iInstruction[7:0]))
  );

  // Datapath relations and branch condition
  assert property (disable iff (iReset)                 oA == sub);
  assert property (disable iff (iReset || !past_valid)  sub == $past(D) - $past(S));
  assert property (disable iff (iReset || !past_valid)  leq == ($past(sub)[31] || ($past(sub)==32'd0)));
  assert property (disable iff (iReset)                 oJump == leq);

  // Next IP and IP update rules
  assert property (disable iff (iReset || !past_valid)
    oNextIP == ($past(leq) ? $past(B) : $past(oIP) + 32'd4)
  );
  assert property (disable iff (iReset || !past_valid)
    oIP == ($past(oJump) ? $past(B) : $past(oIP) + 32'd4)
  );

  // IP and NextIP must match (since oJump == leq)
  assert property (disable iff (iReset) oIP == oNextIP);

  // oB is a one-cycle delayed copy of internal B
  assert property (disable iff (iReset || !past_valid) oB == $past(B));

  // Functional coverage
  cover property (disable iff (iReset || !past_valid)  $past(leq) && (oIP == $past(B)));            // branch taken
  cover property (disable iff (iReset || !past_valid) !$past(leq) && (oIP == $past(oIP) + 32'd4));  // fall-through
  cover property (disable iff (iReset || !past_valid)  $past(sub)==32'd0);                          // zero result
  cover property (disable iff (iReset || !past_valid)  $past(sub)[31]);                             // negative result
  cover property (disable iff (iReset || !past_valid) !$past(sub)[31] && ($past(sub)!=32'd0));      // positive result

endmodule

bind subleq subleq_sva
(
  .iClock(iClock),
  .iReset(iReset),
  .iInstruction(iInstruction),
  .oIP(oIP),
  .oA(oA),
  .oB(oB),
  .oNextIP(oNextIP),
  .oJump(oJump),
  .S(S),
  .D(D),
  .B(B),
  .sub(sub),
  .leq(leq)
);
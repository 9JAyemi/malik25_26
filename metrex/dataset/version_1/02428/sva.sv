// SVA checker for opModule
// Concise, high-quality checks + essential coverage
module opModule_sva (
  input logic        clk,
  input logic [3:0]  iA,
  input logic [3:0]  iB,
  input logic        iC,
  input logic [3:0]  oResult
);

  // Guard $past-based checks
  logic initdone;
  initial initdone = 1'b0;
  always_ff @(posedge clk) initdone <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Core functional correctness (registered: next cycle equals op of this cycle)
  assert property (cb disable iff (!initdone)
    oResult == ( $past(iC) ? ($past(iA) | $past(iB)) : ($past(iA) & $past(iB)) )
  ) else $error("oResult does not match registered AND/OR function of inputs");

  // Stability: if inputs and mode are stable, output must be stable
  assert property (cb disable iff (!initdone)
    ($stable(iA) && $stable(iB) && $stable(iC)) |-> $stable(oResult)
  ) else $error("oResult changed despite stable inputs and mode");

  // No X/Z propagation: known inputs imply known output next cycle
  assert property (cb
    !$isunknown({iA,iB,iC}) |=> !$isunknown(oResult)
  ) else $error("oResult is X/Z with known inputs");

  // Functional coverage
  cover property (cb (iC==0) && ((iA & iB)==4'h0)); // AND -> all zeros
  cover property (cb (iC==0) && ((iA & iB)==4'hF)); // AND -> all ones
  cover property (cb (iC==1) && ((iA | iB)==4'h0)); // OR  -> all zeros
  cover property (cb (iC==1) && ((iA | iB)==4'hF)); // OR  -> all ones

  // Mode toggle coverage
  cover property (cb (iC==0) ##1 (iC==1));
  cover property (cb (iC==1) ##1 (iC==0));

  // Observe output change on mode toggle with same operands when AND!=OR
  cover property (cb
    (iC==0 && $stable(iA) && $stable(iB) && ((iA & iB)!=(iA | iB)))
    ##1 (iC==1 && $stable(iA) && $stable(iB))
    ##1 (oResult != $past(oResult))
  );

endmodule

// Bind into DUT
bind opModule opModule_sva u_opModule_sva (
  .clk(clk),
  .iA(iA),
  .iB(iB),
  .iC(iC),
  .oResult(oResult)
);
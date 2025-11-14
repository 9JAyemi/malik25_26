// SVA for edgedetect. Bind this checker to the DUT.
// Covers both registered and unregistered modes concisely and thoroughly.

module edgedetect_sva
  #(parameter bit REGISTERED = 0)  // 1 when DUT parameter registered == "TRUE"
  (
    input  logic iCLK,
    input  logic iRST,
    input  logic iSIG,
    input  logic oRE,
    input  logic oFE,
    input  logic oRFE,
    // Optional internal tap for extra sanity (connect to DUT's internal 'delay')
    input  logic delay
  );

  default clocking cb @(posedge iCLK); endclocking

  // Internal pipeline sanity
  assert property (cb iRST |-> delay == 1'b0);
  assert property (cb disable iff (iRST || $past(iRST)) delay == $past(iSIG));

  // Reseted outputs in registered mode
  assert property (cb (REGISTERED && iRST) |-> !oRE && !oFE && !oRFE);

  // Mutual exclusivity and combined edge flag
  assert property (cb disable iff (iRST) !(oRE && oFE));
  assert property (cb disable iff (iRST) oRFE == (oRE || oFE));

  // One-cycle pulse width on outputs (relative to clk)
  assert property (cb disable iff (iRST) oRE  |-> ##1 !oRE);
  assert property (cb disable iff (iRST) oFE  |-> ##1 !oFE);
  assert property (cb disable iff (iRST) oRFE |-> ##1 !oRFE);

  // Functional correctness vs sampled input
  generate
    if (REGISTERED) begin : GEN_REG
      // Pulse reflects transition between the two previous samples
      assert property (cb disable iff (iRST || $past(iRST) || $past($past(iRST)))
        oRE  == ($past(iSIG)  && !$past($past(iSIG))));
      assert property (cb disable iff (iRST || $past(iRST) || $past($past(iRST)))
        oFE  == (!$past(iSIG) &&  $past($past(iSIG))));
      assert property (cb disable iff (iRST || $past(iRST) || $past($past(iRST)))
        oRFE == ($past(iSIG)  ^   $past($past(iSIG))));
    end else begin : GEN_COMB
      // Pulse reflects transition between current and previous samples
      assert property (cb disable iff (iRST || $past(iRST))
        oRE  == ( iSIG && !$past(iSIG)));
      assert property (cb disable iff (iRST || $past(iRST))
        oFE  == (!iSIG &&  $past(iSIG)));
      assert property (cb disable iff (iRST || $past(iRST))
        oRFE == ( iSIG ^   $past(iSIG)));
    end
  endgenerate

  // Coverage: see both edges and combined flag
  cover property (cb !iRST && oRE);
  cover property (cb !iRST && oFE);
  cover property (cb !iRST && oRFE);
  // Edge ordering coverage
  cover property (cb !iRST ##1 oRE ##1 oFE);
  cover property (cb !iRST ##1 oFE ##1 oRE);

endmodule

// Example bind (tools typically allow string== comparison to produce a 1/0):
// bind edgedetect edgedetect_sva #(.REGISTERED(registered=="TRUE"))
//   edgedetect_sva_i (.*, .delay(delay));
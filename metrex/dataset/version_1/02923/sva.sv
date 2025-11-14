// SVA checker for inverter
module inverter_sva (input logic din, dout);

  // Functional equivalence at all times (4-state aware)
  assert property (@(din or dout) (dout === ~din))
    else $error("inverter_sva: dout != ~din");

  // Directional edge checks (same-timestep response)
  assert property (@(posedge din) |=> $fell(dout))
    else $error("inverter_sva: dout did not fall on din rise");
  assert property (@(negedge din) |=> $rose(dout))
    else $error("inverter_sva: dout did not rise on din fall");

  // Basic coverage: both steady values observed
  cover property (@(din or dout) (din==1'b0 && dout==1'b1));
  cover property (@(din or dout) (din==1'b1 && dout==1'b0));

  // Transition coverage: both edge directions seen
  cover property (@(posedge din) $fell(dout));
  cover property (@(negedge din) $rose(dout));

endmodule

// Bind into DUT
bind inverter inverter_sva u_inverter_sva(.din(din), .dout(dout));
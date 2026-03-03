// SVA for dff: functional correctness, no-glitching, and basic coverage
module dff_sva (input logic D, CLK, Q);

  default clocking cb @(posedge CLK); endclocking

  bit started;
  initial started = 0;
  always @(posedge CLK) started <= 1;

  // Functional: on each clock, Q holds the previous-cycle D (when that D was known)
  assert property (started && !$isunknown($past(D)) |-> (Q == $past(D)))
    else $error("dff: Q != past(D)");

  // Q may only change coincident with a clock rising edge (no glitches)
  assert property (@(posedge Q) $rose(CLK))
    else $error("dff: Q rose without CLK rise");
  assert property (@(negedge Q) $rose(CLK))
    else $error("dff: Q fell without CLK rise");

  // Flag unknown data at sampling edge
  assert property (started |-> !$isunknown(D))
    else $error("dff: D is X/Z at CLK edge");

  // Coverage: observe both Q transitions and a valid capture
  cover property (@(posedge Q) 1);
  cover property (@(negedge Q) 1);
  cover property (started && !$isunknown(D) ##1 (Q == $past(D)));

endmodule

bind dff dff_sva sva_inst (.D(D), .CLK(CLK), .Q(Q));
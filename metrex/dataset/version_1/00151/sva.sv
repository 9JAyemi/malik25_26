// SVA for dff_with_reset: concise, high-quality checks and coverage
module dff_with_reset_sva (input logic D, CLK, RST, Q);

  // Async reset: clears immediately and holds while asserted
  assert property (@(posedge RST) ##0 (Q == 1'b0));
  assert property (RST |-> (Q == 1'b0));

  // After reset deasserts, Q must remain 0 until the next CLK edge
  assert property ( $fell(RST) |-> (Q == 1'b0 until_with $rose(CLK)) );

  // Clocked behavior: on CLK when not in reset, Q captures D
  assert property (@(posedge CLK) !RST |-> (Q == $past(D)));

  // If CLK rises during reset, Q must be 0
  assert property (@(posedge CLK) RST |-> (Q == 1'b0));

  // Q may only change on posedge CLK or posedge RST
  assert property ( $changed(Q) |-> ($rose(CLK) || $rose(RST)) );

  // Basic X-checks at critical sample points
  assert property (@(posedge CLK) !$isunknown({D,RST}));
  assert property (@(posedge RST) !$isunknown(RST));

  // Coverage: reset pulses and data captures of both 0 and 1
  cover property ($rose(RST));
  cover property ($fell(RST));
  cover property (@(posedge CLK) !RST && (Q == $past(D)));
  cover property (@(posedge CLK) !RST && $past(D)==1'b0 && Q==1'b0);
  cover property (@(posedge CLK) !RST && $past(D)==1'b1 && Q==1'b1);

endmodule

bind dff_with_reset dff_with_reset_sva sva_inst (.D(D), .CLK(CLK), .RST(RST), .Q(Q));
// SVA for mydff: concise, high-quality checks and coverage
module mydff_sva (
  input logic D,
  input logic CLK,
  input logic R,
  input logic Q,
  input logic Qbar
);

  default clocking cb @ (posedge CLK); endclocking

  // Sanity: control/data known when sampled
  assert property (@(posedge CLK) !$isunknown(R));
  assert property (@(posedge CLK) R |-> !$isunknown(D));

  // Async reset forces Q=0 immediately after the event (post-NBA)
  assert property (@(negedge R) ##0 (Q == 1'b0));

  // While in reset, Q must be 0 at every clock
  assert property ( !R |-> (Q == 1'b0) );

  // With reset deasserted, Q captures D on the clock edge (post-NBA)
  assert property ( R |-> ##0 (Q == D) );

  // Complement relationship
  assert property (@(posedge CLK or negedge R) ##0 (Qbar === ~Q));

  // Q cannot change between permitted events (no glitches)
  assert property (@(posedge CLK or negedge R)
                   1 |=> $stable(Q) until_with (posedge CLK or negedge R));

  // Coverage
  cover property (@(negedge R) ##0 (Q == 1'b0));
  cover property (@(posedge R) 1);
  cover property (@(posedge CLK) R && (D==1'b0) ##0 (Q==1'b0));
  cover property (@(posedge CLK) R && (D==1'b1) ##0 (Q==1'b1));
  cover property (@(posedge CLK) R && $changed(D) ##0 $changed(Q));

endmodule

bind mydff mydff_sva u_mydff_sva(.D(D), .CLK(CLK), .R(R), .Q(Q), .Qbar(Qbar));
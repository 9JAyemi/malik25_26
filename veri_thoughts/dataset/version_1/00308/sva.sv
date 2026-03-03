// SVA for dff_preset_clear
module dff_preset_clear_sva (
  input logic D,
  input logic CLK,
  input logic PRE,
  input logic CLR,
  input logic Q,
  input logic Q_N
);
  default clocking cb @(posedge CLK); endclocking

  // Track availability of $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Core next-state function (priority: CLR > PRE > D)
  assert property (
    past_valid |-> Q == ( $past(CLR) ? 1'b0
                       : $past(PRE) ? 1'b1
                       : $past(D) )
  );

  // Complementary outputs
  assert property (Q_N === ~Q);

  // Glitch-free outputs: change only on clock edge
  assert property (@(posedge Q  or negedge Q ) $rose(CLK));
  assert property (@(posedge Q_N or negedge Q_N) $rose(CLK));

  // Coverage: exercise all behaviors
  cover property (past_valid && $past(CLR)                            && Q==1'b0); // clear
  cover property (past_valid && !$past(CLR) && $past(PRE)             && Q==1'b1); // preset
  cover property (past_valid && !$past(CLR) && !$past(PRE) && $past(D)   && Q==1'b1); // normal set
  cover property (past_valid && !$past(CLR) && !$past(PRE) && !$past(D)  && Q==1'b0); // normal reset
  cover property (past_valid && $past(CLR) && $past(PRE)              && Q==1'b0); // both asserted, CLR wins
  cover property (past_valid && $past(Q)==1'b0 && Q==1'b1); // Q 0->1
  cover property (past_valid && $past(Q)==1'b1 && Q==1'b0); // Q 1->0
endmodule

bind dff_preset_clear dff_preset_clear_sva u_dff_preset_clear_sva (
  .D(D), .CLK(CLK), .PRE(PRE), .CLR(CLR), .Q(Q), .Q_N(Q_N)
);
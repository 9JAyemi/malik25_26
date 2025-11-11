// SVA for alu. Bind this file alongside the DUT.
`ifndef ALU_SVA_SV
`define ALU_SVA_SV

module alu_sva
(
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [2:0]  OP,
  input logic [3:0]  Y
);
  // Access to DUT internals via bind: A_reg, B_reg, Y_reg, stage
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Stage legality and alternation
  assert property (disable iff (!past_valid) (stage inside {2'd0,2'd1}));
  assert property (disable iff (!past_valid) (stage==2'd0) |=> (stage==2'd1));
  assert property (disable iff (!past_valid) (stage==2'd1) |=> (stage==2'd0));

  // Input sanity and OP validity when computing
  assert property (disable iff (!past_valid) (stage==2'd0) |-> (!$isunknown(A) && !$isunknown(B) && !$isunknown(OP)));
  assert property (disable iff (!past_valid) (stage==2'd0) |-> (OP inside {3'b000,3'b001,3'b010,3'b011,3'b100}));

  // Register capture/hold behavior
  assert property (disable iff (!past_valid) (stage==2'd0) |-> (A_reg == $past(A) && B_reg == $past(B)));
  assert property (disable iff (!past_valid) (stage==2'd1) |-> ($stable(A_reg) && $stable(B_reg) && $stable(Y_reg)));
  assert property (disable iff (!past_valid) (stage==2'd0) |-> $stable(Y));
  assert property (disable iff (!past_valid) (stage==2'd1) |-> (Y == $past(Y_reg)));
  assert property (disable iff (!past_valid) $changed(Y) |-> (stage==2'd1));

  // ALU function into Y_reg in stage 0 (operands are prior A_reg/B_reg)
  assert property (disable iff (!past_valid)
    (stage==2'd0 && OP==3'b000) |-> (Y_reg == ($past(A_reg) + $past(B_reg))));
  assert property (disable iff (!past_valid)
    (stage==2'd0 && OP==3'b001) |-> (Y_reg == ($past(A_reg) - $past(B_reg))));
  assert property (disable iff (!past_valid)
    (stage==2'd0 && OP==3'b010) |-> (Y_reg == ($past(A_reg) & $past(B_reg))));
  assert property (disable iff (!past_valid)
    (stage==2'd0 && OP==3'b011) |-> (Y_reg == ($past(A_reg) | $past(B_reg))));
  assert property (disable iff (!past_valid)
    (stage==2'd0 && OP==3'b100) |-> (Y_reg == ($past(A_reg) ^ $past(B_reg))));

  // Y_reg must hold when OP is invalid in stage 0
  assert property (disable iff (!past_valid)
    (stage==2'd0 && !(OP inside {3'b000,3'b001,3'b010,3'b011,3'b100})) |-> $stable(Y_reg));

  // End-to-end result check at output (accounts for pipeline timing)
  assert property (disable iff (!past_valid || !$past(past_valid))
    (stage==2'd1 && $past(stage)==2'd0 && ($past(OP) inside {3'b000,3'b001,3'b010,3'b011,3'b100}))
    |-> (Y == ( ($past(OP)==3'b000) ? ($past(A_reg,2)+$past(B_reg,2)) :
                ($past(OP)==3'b001) ? ($past(A_reg,2)-$past(B_reg,2)) :
                ($past(OP)==3'b010) ? ($past(A_reg,2)&$past(B_reg,2)) :
                ($past(OP)==3'b011) ? ($past(A_reg,2)|$past(B_reg,2)) :
                                      ($past(A_reg,2)^$past(B_reg,2)) )));

  // Functional coverage
  cover property (stage==2'd0 ##1 stage==2'd1 ##1 stage==2'd0);
  cover property (stage==2'd0 && OP==3'b000);
  cover property (stage==2'd0 && OP==3'b001);
  cover property (stage==2'd0 && OP==3'b010);
  cover property (stage==2'd0 && OP==3'b011);
  cover property (stage==2'd0 && OP==3'b100);
  // Add/sub overflow scenarios
  cover property ( (stage==2'd0 && OP==3'b000) ##1 (stage==2'd1) &&
                   (({1'b0,$past(A_reg)} + {1'b0,$past(B_reg)})[4]) );
  cover property ( (stage==2'd0 && OP==3'b001) ##1 (stage==2'd1) &&
                   (({1'b0,$past(A_reg)} - {1'b0,$past(B_reg)})[4]) );

endmodule

bind alu alu_sva u_alu_sva (.*);
`endif
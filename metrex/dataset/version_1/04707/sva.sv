// SVA for comparator
module comparator_sva (
  input logic        clk,
  input logic [3:0]  A, B,
  input logic        EQ, GT, LT,
  input logic [3:0]  A_reg, B_reg,
  input logic [1:0]  stage
);
  default clocking cb @(posedge clk); endclocking

  // Stage legality and toggling (after first valid past)
  assert property (!$isunknown($past(stage)) |-> stage inside {2'b00,2'b01});
  assert property (!$isunknown($past(stage)) |-> stage != $past(stage));

  // Transparent/hold semantics
  assert property (stage==0 |-> (A_reg==A && B_reg==B));
  assert property (stage==1 |-> ($stable(A_reg) && $stable(B_reg)));
  assert property ($rose(stage[0]) |-> (A_reg==$past(A) && B_reg==$past(B)));

  // Outputs defined, correct, exclusive, and stable during hold
  assert property (!$isunknown({A_reg,B_reg}) |-> !$isunknown({EQ,GT,LT}));
  assert property (!$isunknown({A_reg,B_reg}) |-> (
                     (EQ == (A_reg==B_reg)) &&
                     (GT == (A_reg> B_reg)) &&
                     (LT == (A_reg< B_reg))
                   ));
  assert property (!$isunknown({EQ,GT,LT}) |-> $onehot({EQ,GT,LT}));
  assert property (!$isunknown({A_reg,B_reg}) |-> $onehot({A_reg==B_reg, A_reg>B_reg, A_reg<B_reg}));
  assert property (stage==1 |-> $stable({EQ,GT,LT}));

  // Coverage
  cover property (stage==0 ##1 stage==1 ##1 stage==0);
  cover property (!$isunknown({EQ,GT,LT}) && EQ);
  cover property (!$isunknown({EQ,GT,LT}) && GT);
  cover property (!$isunknown({EQ,GT,LT}) && LT);
endmodule

bind comparator comparator_sva u_comparator_sva (
  .clk(clk),
  .A(A), .B(B),
  .EQ(EQ), .GT(GT), .LT(LT),
  .A_reg(A_reg), .B_reg(B_reg),
  .stage(stage)
);
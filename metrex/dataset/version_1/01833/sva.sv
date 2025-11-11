// SVA for priority_encoder
// Binds into the DUT and checks pipeline alignment, decode mapping, hold-on-invalid,
// plus end-to-end functional coverage.

module priority_encoder_sva (
  input logic        clk,
  input logic [7:0]  in,
  input logic [7:0]  in_reg,
  input logic [2:0]  out_reg,
  input logic [2:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // History guards
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // Pipeline alignment
  assert property (past1 |-> in_reg === $past(in));
  assert property (past1 |-> out    === $past(out_reg));

  // Decode mapping on valid one-hot (sampled in in_reg)
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0000_0001 |-> out_reg==3'd0);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0000_0010 |-> out_reg==3'd1);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0000_0100 |-> out_reg==3'd2);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0000_1000 |-> out_reg==3'd3);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0001_0000 |-> out_reg==3'd4);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0010_0000 |-> out_reg==3'd5);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b0100_0000 |-> out_reg==3'd6);
  assert property (past1 && !$isunknown($past(in_reg)) && $onehot($past(in_reg)) && $past(in_reg)==8'b1000_0000 |-> out_reg==3'd7);

  // Hold behavior on invalid/zero/X (default branch)
  assert property (past1 && (!$onehot($past(in_reg)) || $isunknown($past(in_reg))) |-> out_reg === $past(out_reg));

  // End-to-end functional coverage (in -> out after 2 cycles)
  cover property (past2 && $past(in,2)==8'b0000_0001 ##0 (out==3'd0));
  cover property (past2 && $past(in,2)==8'b0000_0010 ##0 (out==3'd1));
  cover property (past2 && $past(in,2)==8'b0000_0100 ##0 (out==3'd2));
  cover property (past2 && $past(in,2)==8'b0000_1000 ##0 (out==3'd3));
  cover property (past2 && $past(in,2)==8'b0001_0000 ##0 (out==3'd4));
  cover property (past2 && $past(in,2)==8'b0010_0000 ##0 (out==3'd5));
  cover property (past2 && $past(in,2)==8'b0100_0000 ##0 (out==3'd6));
  cover property (past2 && $past(in,2)==8'b1000_0000 ##0 (out==3'd7));
  cover property (past2 && (!$onehot($past(in,2)) || $isunknown($past(in,2))) ##0 (out === $past(out)));

endmodule

bind priority_encoder priority_encoder_sva u_priority_encoder_sva (
  .clk(clk),
  .in(in),
  .in_reg(in_reg),
  .out_reg(out_reg),
  .out(out)
);
// SVA for urn_gen. Bind this checker to the DUT to verify functionality and provide concise coverage.

bind urn_gen urn_gen_sva i_urn_gen_sva(
  .clk(clk), .rst(rst),
  .s1(s1), .s2(s2), .s3(s3),
  .urn(urn), .urn_reg(urn_reg),
  .b1(b1), .b2(b2), .b3(b3),
  .new_s1(new_s1), .new_s2(new_s2), .new_s3(new_s3)
);

module urn_gen_sva(
  input logic        clk, rst,
  input logic [63:0] s1, s2, s3,
  input logic [63:0] urn, urn_reg,
  input logic [63:0] b1, b2, b3,
  input logic [63:0] new_s1, new_s2, new_s3
);

  // Output mirrors internal register
  assert property (@(posedge clk) urn == urn_reg);

  // Reset loads constants
  assert property (@(posedge clk)
    rst |-> (s1==64'd1234 && s2==64'd5678 && s3==64'd9012 && urn_reg==64'd0));

  // While held in reset, constants persist
  assert property (@(posedge clk)
    rst && $past(rst) |-> (s1==64'd1234 && s2==64'd5678 && s3==64'd9012 && urn_reg==64'd0));

  // Combinational equations hold (and no Xs when s* known)
  assert property (@(posedge clk)
    !rst && !$isunknown(s1) |->
      (b1 == (((s1<<13)^s1)>>19)) &&
      (new_s1 == (((s1 & 64'hfffffffffffffffe) << 12) ^ b1)));

  assert property (@(posedge clk)
    !rst && !$isunknown(s2) |->
      (b2 == (((s2<<2)^s2)>>25)) &&
      (new_s2 == (((s2 & 64'hfffffffffffffff8) << 4) ^ b2)));

  assert property (@(posedge clk)
    !rst && !$isunknown(s3) |->
      (b3 == (((s3<<3)^s3)>>11)) &&
      (new_s3 == (((s3 & 64'hfffffffffffffff0) << 17) ^ b3)));

  // Sequential updates (one-cycle latency due to NBA)
  assert property (@(posedge clk)
    $past(1'b1) && !$past(rst) |->
      (s1 == $past(new_s1)) &&
      (s2 == $past(new_s2)) &&
      (s3 == $past(new_s3)) &&
      (urn_reg == $past(new_s1 ^ new_s2 ^ new_s3)));

  // After one non-reset cycle, urn_reg equals current s1^s2^s3
  assert property (@(posedge clk)
    $past(1'b1) && !$past(rst) |-> urn_reg == (s1 ^ s2 ^ s3));

  // Knownness: no X/Z one cycle after reset deassert
  assert property (@(posedge clk)
    $fell(rst) |-> ##1
      (!$isunknown({s1,s2,s3,urn_reg,urn,b1,b2,b3,new_s1,new_s2,new_s3})));

  // Knownness even during reset (driven constants/comb)
  assert property (@(posedge clk)
    rst |-> !$isunknown({s1,s2,s3,urn_reg,urn,b1,b2,b3,new_s1,new_s2,new_s3}));

  // -------- Coverage (concise, meaningful) --------
  // See at least one reset then run
  cover property (@(posedge clk) rst ##1 !rst ##1 !rst);

  // Observe a state update and urn change after coming out of reset
  cover property (@(posedge clk)
    $fell(rst) ##1 !rst ##1 ($changed(s1) || $changed(s2) || $changed(s3)) && $changed(urn_reg));

  // Observe non-zero output after leaving reset
  cover property (@(posedge clk)
    $fell(rst) ##2 (urn != 64'd0));

  // Exercise multiple consecutive non-reset cycles
  cover property (@(posedge clk) !rst [*5]);

endmodule
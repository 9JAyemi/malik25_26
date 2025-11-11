// SVA for top_module + sub-blocks (bind-ready). Concise but checks key intent and corner cases.

// ------------ Assertions bound into top_module ------------
module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [31:0]  a,
  input logic [31:0]  b,
  input logic         select,
  input logic [31:0]  adder_out,
  input logic [4:0]   priority_enc_out,
  input logic [31:0]  sum,              // internal
  input logic [2:0]   high_bit_pos,     // internal
  input logic [7:0]   high_bit_chunk    // output
);
  default clocking cb @(posedge clk); endclocking

  // Reset brings regs to 0 on next clk
  ap_reset_state: assert property (@(posedge clk) reset |-> (sum==32'h0 && high_bit_pos==3'h0));

  default disable iff (reset);

  // Registered control behavior
  ap_sum_sel1:  assert property (select  |=> sum == adder_out);
  ap_sum_sel0:  assert property (!select |=> sum == a + b);
  ap_hbp_sel1:  assert property (select  |=> high_bit_pos == priority_enc_out[2:0]);
  ap_hbp_sel0:  assert property (!select |=> high_bit_pos == 3'd0);

  // Sanity: no X on key signals
  ap_no_x:      assert property (!$isunknown({a,b,select,adder_out,priority_enc_out,sum,high_bit_pos,high_bit_chunk}));

  // Priority encoder width/safety
  ap_pe_width:  assert property (priority_enc_out[4] == 1'b0);
  // Prevent truncation errors feeding 3-bit pos (design only supports 0..3)
  ap_hbp_range: assert property (select |-> priority_enc_out <= 5'd3);

  // High-bit chunk decode (combinational behavior sampled on clk)
  ap_hbc0:      assert property (high_bit_pos==3'd0 |-> high_bit_chunk == sum[7:0]);
  ap_hbc1:      assert property (high_bit_pos==3'd1 |-> high_bit_chunk == sum[15:8]);
  ap_hbc2:      assert property (high_bit_pos==3'd2 |-> high_bit_chunk == sum[23:16]);
  ap_hbc3:      assert property (high_bit_pos==3'd3 |-> high_bit_chunk == sum[31:24]);
  ap_hbc_def:   assert property ((high_bit_pos>3)   |-> high_bit_chunk == 8'h00);

  // The 32-bit adder output should equal a+b (exposes adder_32 issues)
  ap_adder32_ref: assert property (adder_out == a + b);

  // Priority encoder truth-table for the specified patterns (exposes mapping issues)
  ap_pe_map_f:  assert property ((adder_out==32'hFFFF_FFFF) |-> priority_enc_out[3:0]==4'hF);
  ap_pe_map_e:  assert property ((adder_out==32'h7FFF_FFFF) |-> priority_enc_out[3:0]==4'hE);
  ap_pe_map_d:  assert property ((adder_out==32'h3FFF_FFFF) |-> priority_enc_out[3:0]==4'hD);
  ap_pe_map_c:  assert property ((adder_out==32'h1FFF_FFFF) |-> priority_enc_out[3:0]==4'hC);
  ap_pe_map_b:  assert property ((adder_out==32'h0FFF_FFFF) |-> priority_enc_out[3:0]==4'hB);
  ap_pe_map_a:  assert property ((adder_out==32'h07FF_FFFF) |-> priority_enc_out[3:0]==4'hA);
  ap_pe_map_9:  assert property ((adder_out==32'h03FF_FFFF) |-> priority_enc_out[3:0]==4'h9);
  ap_pe_map_8:  assert property ((adder_out==32'h01FF_FFFF) |-> priority_enc_out[3:0]==4'h8);
  ap_pe_map_7:  assert property ((adder_out==32'h00FF_FFFF) |-> priority_enc_out[3:0]==4'h7);
  ap_pe_map_6:  assert property ((adder_out==32'h007F_FFFF) |-> priority_enc_out[3:0]==4'h6);
  ap_pe_map_5:  assert property ((adder_out==32'h003F_FFFF) |-> priority_enc_out[3:0]==4'h5);
  ap_pe_map_4:  assert property ((adder_out==32'h001F_FFFF) |-> priority_enc_out[3:0]==4'h4);
  ap_pe_map_3:  assert property ((adder_out==32'h000F_FFFF) |-> priority_enc_out[3:0]==4'h3);
  ap_pe_map_2:  assert property ((adder_out==32'h0007_FFFF) |-> priority_enc_out[3:0]==4'h2);
  ap_pe_map_1:  assert property ((adder_out==32'h0003_FFFF) |-> priority_enc_out[3:0]==4'h1);
  ap_pe_map_0:  assert property ((!(adder_out inside {
                                      32'hFFFF_FFFF,32'h7FFF_FFFF,32'h3FFF_FFFF,32'h1FFF_FFFF,
                                      32'h0FFF_FFFF,32'h07FF_FFFF,32'h03FF_FFFF,32'h01FF_FFFF,
                                      32'h00FF_FFFF,32'h007F_FFFF,32'h003F_FFFF,32'h001F_FFFF,
                                      32'h000F_FFFF,32'h0007_FFFF,32'h0003_FFFF}))
                                |-> priority_enc_out[3:0]==4'h0);

  // Coverage
  cp_reset_release:     cover property (reset ##1 !reset);
  cp_select_01:         cover property (!select ##1 select);
  cp_select_10:         cover property ( select ##1 !select);
  cp_hbp_each0:         cover property (high_bit_pos==3'd0);
  cp_hbp_each1:         cover property (high_bit_pos==3'd1);
  cp_hbp_each2:         cover property (high_bit_pos==3'd2);
  cp_hbp_each3:         cover property (high_bit_pos==3'd3);
  cp_pe_out_gt3:        cover property (select && priority_enc_out > 5'd3);
endmodule

// ------------ Assertions bound into adder_32 ------------
module adder_32_sva (
  input logic        clk,
  input logic        reset,
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] out,
  input logic [8:0]  sum1, sum2, sum3, sum4
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Each 8-bit block sum and carry propagation must be correct
  a_blk0: assert property (sum1 == a[7:0]   + b[7:0]   + 1'b0);
  a_blk1: assert property (sum2 == a[15:8]  + b[15:8]  + sum1[8]);
  a_blk2: assert property (sum3 == a[23:16] + b[23:16] + sum2[8]);
  a_blk3: assert property (sum4 == a[31:24] + b[31:24] + sum3[8]);

  // Full 32-bit result must match concatenation and arithmetic intent
  a_out_concat: assert property (out == {sum4[7:0], sum3[7:0], sum2[7:0], sum1[7:0]});
  a_out_gold:   assert property (out == a + b);

  // Sanity and corner coverage
  a_no_x:       assert property (!$isunknown({a,b,out,sum1,sum2,sum3,sum4}));
  c_carry_out:  cover  property (sum4[8] == 1'b1);
endmodule

// ------------ Bind statements ------------
bind top_module  top_module_sva u_top_module_sva (
  .clk(clk), .reset(reset), .a(a), .b(b), .select(select),
  .adder_out(adder_out), .priority_enc_out(priority_enc_out),
  .sum(sum), .high_bit_pos(high_bit_pos), .high_bit_chunk(high_bit_chunk)
);

bind adder_32   adder_32_sva u_adder_32_sva (
  .clk(clk), .reset(reset), .a(a), .b(b), .out(out),
  .sum1(sum1), .sum2(sum2), .sum3(sum3), .sum4(sum4)
);
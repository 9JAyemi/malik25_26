// SVA for des_comp_gen_fx_color
// Bind this checker to the DUT:
//   bind des_comp_gen_fx_color des_comp_gen_fx_color_sva sva_inst (.*);

module des_comp_gen_fx_color_sva
(
  input  logic               clk,
  input  logic               rstn,

  input  logic signed [31:0] dx_fx,
  input  logic signed [31:0] dy_fx,
  input  logic        [95:0] cmp_i,

  input  logic        [7:0]  curr_i,

  // Internal DUT nets/regs
  input  logic signed [57:0] ix,
  input  logic signed [57:0] iy,
  input  logic signed [57:0] ixy,
  input  logic signed [19:0] curr,

  input  logic        [17:0] sp_fx,
  input  logic signed [25:0] idx_fx,
  input  logic signed [25:0] idy_fx
);

  // Simple past-valid tracker for safe $past usage
  logic [2:0] past_v;
  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) past_v <= '0;
    else       past_v <= {past_v[1:0], 1'b1};
  end
  wire past1 = past_v[0];
  wire past2 = past_v[1];

  // Stage checks: multipliers, adder, and final accumulation
  // ix = dx_fx * idx_fx (sampled previous cycle due to NBA semantics)
  assert property (@(posedge clk) disable iff (!rstn)
    past1 |-> ix == ( $signed($past(dx_fx)) * $signed($past(idx_fx)) )
  ) else $error("ix mismatch with dx_fx*idx_fx");

  // iy = dy_fx * idy_fx
  assert property (@(posedge clk) disable iff (!rstn)
    past1 |-> iy == ( $signed($past(dy_fx)) * $signed($past(idy_fx)) )
  ) else $error("iy mismatch with dy_fx*idy_fx");

  // ixy = previous ix + previous iy
  assert property (@(posedge clk) disable iff (!rstn)
    past1 |-> ixy == ($past(ix) + $past(iy))
  ) else $error("ixy mismatch with ix+iy");

  // curr = previous ixy[35:16] + sp_fx (current)
  assert property (@(posedge clk) disable iff (!rstn)
    past1 |-> curr == ($past(ixy[35:16]) + {2'b00, sp_fx})
  ) else $error("curr mismatch with ixy[35:16]+sp_fx");

  // Saturation/quantization mapping to curr_i
  assert property (@(posedge clk) disable iff (!rstn)
    curr[19] |-> (curr_i == 8'h00)
  ) else $error("Underflow mapping to curr_i failed");

  assert property (@(posedge clk) disable iff (!rstn)
    (!curr[19] && curr[18]) |-> (curr_i == 8'hff)
  ) else $error("Overflow mapping to curr_i failed");

  assert property (@(posedge clk) disable iff (!rstn)
    (!curr[19] && !curr[18]) |-> (curr_i == curr[17:10])
  ) else $error("Normal mapping to curr_i failed");

  // Zero input to FP-to-fixed converters must yield zero (handles +0 and -0)
  // sp_fx: cmp_i[95:64]
  assert property (@(posedge clk) disable iff (!rstn)
    (cmp_i[94:64] == 31'b0) |-> (sp_fx == 18'd0)
  ) else $error("flt_fx_8p10 zero input did not produce zero");

  // idx_fx: cmp_i[63:32]
  assert property (@(posedge clk) disable iff (!rstn)
    (cmp_i[62:32] == 31'b0) |-> (idx_fx == 26'sd0)
  ) else $error("flt_fx_16p10 (idx) zero input did not produce zero");

  // idy_fx: cmp_i[31:0]
  assert property (@(posedge clk) disable iff (!rstn)
    (cmp_i[30:0] == 31'b0) |-> (idy_fx == 26'sd0)
  ) else $error("flt_fx_16p10 (idy) zero input did not produce zero");

  // X/Z sanitation after two cycles out of reset
  assert property (@(posedge clk) disable iff (!rstn)
    past2 |-> (!$isunknown(ix) && !$isunknown(iy) && !$isunknown(ixy) &&
               !$isunknown(curr) && !$isunknown(curr_i))
  ) else $error("Unknown (X/Z) detected on internal regs or output");

  // Functional coverage
  cover property (@(posedge clk) disable iff (!rstn) curr[19]);                // underflow path
  cover property (@(posedge clk) disable iff (!rstn) (!curr[19] && curr[18])); // overflow path
  cover property (@(posedge clk) disable iff (!rstn) (!curr[19] && !curr[18])); // normal path

  // Hit some output extremes and a mid value
  cover property (@(posedge clk) disable iff (!rstn) curr_i == 8'h00);
  cover property (@(posedge clk) disable iff (!rstn) curr_i == 8'hff);
  cover property (@(posedge clk) disable iff (!rstn) curr_i == 8'h80);

  // Exercise negative-zero cases of converters
  cover property (@(posedge clk) disable iff (!rstn)
    (cmp_i[95] && (cmp_i[94:64]==31'b0) && (sp_fx==18'd0))
  );
  cover property (@(posedge clk) disable iff (!rstn)
    (cmp_i[63] && (cmp_i[62:32]==31'b0) && (idx_fx==26'sd0))
  );
  cover property (@(posedge clk) disable iff (!rstn)
    (cmp_i[31] && (cmp_i[30:0]==31'b0) && (idy_fx==26'sd0))
  );

endmodule

// Suggested bind (place in a testbench or a package included by TB)
// bind des_comp_gen_fx_color des_comp_gen_fx_color_sva sva_inst (.*);
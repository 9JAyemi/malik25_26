// SVA checker for gray_code_converter
module gray_code_converter_sva (
  input  logic [3:0] data_in,
  input  logic [3:0] gray_out,
  input  logic [3:0] stage1_out,
  input  logic [3:0] stage2_out
);

  // No X/Z on outputs if inputs are clean
  ap_no_x: assert property (!$isunknown(data_in) |-> (!$isunknown(stage1_out) && !$isunknown(stage2_out) && !$isunknown(gray_out)));

  // Stage 1 equations (guarded)
  ap_s1: assert property (
    !$isunknown(data_in) |-> (stage1_out == {data_in[3]^data_in[2], data_in[2]^data_in[1], data_in[1]^data_in[0], data_in[0]})
  );

  // Stage 2 equations (guarded)
  ap_s2_b0: assert property (!$isunknown(stage1_out) |-> (stage2_out[0] == stage1_out[0]));
  ap_s2_b1: assert property (!$isunknown(stage1_out) |-> (stage2_out[1] == (stage1_out[1] ^ stage1_out[0])));
  ap_s2_b2: assert property (!$isunknown(stage1_out) |-> (stage2_out[2] == (stage1_out[2] ^ stage1_out[1])));
  ap_s2_b3: assert property (!$isunknown(stage1_out) |-> (stage2_out[3] == (stage1_out[3] ^ stage1_out[2])));

  // Output equals Stage 2 (guarded)
  ap_out_eq_s2: assert property (!$isunknown(stage2_out) |-> (gray_out == stage2_out));

  // Spec check: standard binary->Gray (gray = bin ^ (bin>>1))
  logic [3:0] exp_gray;
  assign exp_gray = {data_in[3], data_in[3]^data_in[2], data_in[2]^data_in[1], data_in[1]^data_in[0]};
  ap_spec: assert property (!$isunknown(data_in) |-> (gray_out == exp_gray));

  // Output only changes when input changes (no spurious toggles)
  ap_change_dep: assert property ($changed(gray_out) |-> ##0 $changed(data_in));

  // Coverage: hit all 16 input values
  genvar i;
  generate
    for (i=0; i<16; i++) begin : cv_in_vals
      cp_in_val: cover property (data_in == i[3:0]);
    end
  endgenerate

  // Coverage: each output bit toggles both ways
  genvar b;
  generate
    for (b=0; b<4; b++) begin : cv_out_toggles
      cp_out_01: cover property ($rose(gray_out[b]));
      cp_out_10: cover property ($fell(gray_out[b]));
    end
  endgenerate

endmodule

// Bind into DUT (allows access to internal regs)
bind gray_code_converter gray_code_converter_sva
  (.data_in(data_in),
   .gray_out(gray_out),
   .stage1_out(stage1_out),
   .stage2_out(stage2_out));
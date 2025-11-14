// SVA for mux_multiply and its submodules (concise, with key checks and coverage)

module mux_multiply_sva;
  // Bound into mux_multiply; has access to internal nets
  // Clockless concurrent assertions sample on any input change
  // Functional correctness
  ap_mux_sel:   assert property (@(in_0 or in_1 or sel) selected_input == (sel ? in_1 : in_0));
  ap_mult_func: assert property (@(in_0 or in_1 or sel) product == selected_input * selected_input);
  ap_out_conn:  assert property (@(in_0 or in_1 or sel) out == product);
  ap_out_func:  assert property (@(in_0 or in_1 or sel) out == (sel ? in_1 : in_0) * (sel ? in_1 : in_0));
  // Range and X-prop
  ap_range:     assert property (@(in_0 or in_1 or sel) out <= 8'd225);
  ap_no_x:      assert property (@(in_0 or in_1 or sel) !$isunknown({in_0,in_1,sel}) |-> !$isunknown({selected_input,product,out}));
  // Coverage
  cp_sel0:      cover  property (@(negedge sel) out == in_0*in_0);
  cp_sel1:      cover  property (@(posedge sel) out == in_1*in_1);
  cp_min0:      cover  property (@(in_0 or in_1 or sel) sel==0 && in_0==4'd0  && out==8'd0);
  cp_max1:      cover  property (@(in_0 or in_1 or sel) sel==1 && in_1==4'd15 && out==8'd225);
  cp_mid:       cover  property (@(in_0 or in_1 or sel) ((sel==0 && in_0==4'd8) || (sel==1 && in_1==4'd8)) && out==8'd64);
endmodule

module mux2to1_sva;
  ap_mux:       assert property (@(in_0 or in_1 or sel) out == (sel ? in_1 : in_0));
  ap_mux_no_x:  assert property (@(in_0 or in_1 or sel) !$isunknown({in_0,in_1,sel}) |-> !$isunknown(out));
  cp_sel0:      cover  property (@(negedge sel) out == in_0);
  cp_sel1:      cover  property (@(posedge sel) out == in_1);
endmodule

module multiplier_sva;
  ap_mul:       assert property (@(in_0 or in_1) out == in_0 * in_1);
  ap_mul_rng:   assert property (@(in_0 or in_1) out <= 8'd225);
  ap_mul_no_x:  assert property (@(in_0 or in_1) !$isunknown({in_0,in_1}) |-> !$isunknown(out));
  cp_zero:      cover  property (@(in_0 or in_1) (in_0==0 || in_1==0) && out==0);
  cp_max:       cover  property (@(in_0 or in_1) in_0==4'd15 && in_1==4'd15 && out==8'd225);
endmodule

bind mux_multiply mux_multiply_sva mm_sva();
bind mux2to1     mux2to1_sva     mx_sva();
bind multiplier  multiplier_sva  mul_sva();
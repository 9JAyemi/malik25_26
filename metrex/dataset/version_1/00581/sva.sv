// SVA for top_module (clockless, bindable)
// Bind example: bind top_module top_module_sva svatop();

module top_module_sva;
  // All assertions are clockless; sample whenever any operand changes
  default disable iff ($isunknown({in0,in1,enable,cmp_out,dec_out,out}));

  // Comparator correctness
  a_cmp_eq: assert property ( (in0==in1) |-> (cmp_out==4'b0000) );
  a_cmp_gt: assert property ( (in0>in1)  |-> (cmp_out==4'b0001) );
  a_cmp_lt: assert property ( (in0<in1)  |-> (cmp_out==4'b0010) );
  a_cmp_enc_range: assert property ( 1'b1 |-> (cmp_out inside {4'b0000,4'b0001,4'b0010}) );

  // Decoder correctness (one-hot for 0..7 when enabled, zero otherwise)
  a_dec_en_map:   assert property ( enable && (cmp_out<=4'd7) |-> (dec_out == (8'b1 << cmp_out)) );
  a_dec_onehot:   assert property ( enable && (cmp_out<=4'd7) |-> $onehot(dec_out) );
  a_dec_dis_zero: assert property ( !enable |-> (dec_out==8'h00) );

  // Top output mapping (select dec_out bit per compare result) and shaping
  a_top_sel_eq: assert property ( (cmp_out==4'd0) |-> (out == {7'b0, dec_out[0]}) );
  a_top_sel_gt: assert property ( (cmp_out==4'd1) |-> (out == {7'b0, dec_out[1]}) );
  a_top_sel_lt: assert property ( (cmp_out==4'd2) |-> (out == {7'b0, dec_out[2]}) );
  a_top_zero_when_disabled: assert property ( !enable |-> (out==8'h00) );
  a_top_upper_zero:         assert property ( 1'b1    |-> (out[7:1]==7'b0) );

  // End-to-end checks (intended behavior)
  a_e2e_eq: assert property ( enable && (in0==in1) |-> (dec_out==8'b00000001 && out==8'h01) );
  a_e2e_gt: assert property ( enable && (in0>in1)  |-> (dec_out==8'b00000010 && out==8'h01) );
  a_e2e_lt: assert property ( enable && (in0<in1)  |-> (dec_out==8'b00000100 && out==8'h01) );

  // Coverage
  c_eq: cover property ( in0==in1 );
  c_gt: cover property ( in0>in1 );
  c_lt: cover property ( in0<in1 );
  c_en0: cover property ( !enable );
  c_top_sel_eq: cover property ( enable && (cmp_out==4'd0) && out==8'h01 );
  c_top_sel_gt: cover property ( enable && (cmp_out==4'd1) && out==8'h01 );
  c_top_sel_lt: cover property ( enable && (cmp_out==4'd2) && out==8'h01 );
endmodule
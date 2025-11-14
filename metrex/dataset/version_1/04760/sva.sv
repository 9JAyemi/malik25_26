// SVA for the provided design
// Bind these modules to the DUT as shown at the end.

// Assertions on top-level functional behavior (gating and packing)
module sva_control_logic_sv (
  input clk,
  input reset,
  input select,
  input [2:0] vec,
  input [2:0] outv,
  input o2, o1, o0
);
  default clocking @(posedge clk); endclocking

  // Packing consistency always holds
  ap_pack_consistent: assert property ( {o2,o1,o0} === outv );

  // When selected, outputs mirror vec
  ap_sel1_match:     assert property ( select |-> (outv === vec && {o2,o1,o0} === vec) );

  // When not selected, all outputs are zero
  ap_sel0_zero:      assert property ( !select |-> (outv == 3'b000 && {o2,o1,o0} == 3'b000) );

  // Coverage: exercise select states and extremes of vec
  cp_sel_rise:  cover property ( $rose(select) );
  cp_sel_fall:  cover property ( $fell(select) );
  cp_vec_all0:  cover property ( select && vec == 3'b000 && outv == 3'b000 );
  cp_vec_all1:  cover property ( select && vec == 3'b111 && outv == 3'b111 );
  cp_masking:   cover property ( !select && vec == 3'b111 && outv == 3'b000 && {o2,o1,o0} == 3'b000 );
endmodule

// Assertions for the binary counter behavior
module sva_binary_counter_sv (
  input clk,
  input reset,
  input [3:0] q
);
  default clocking @(posedge clk); endclocking

  // Synchronous reset
  ap_cnt_reset: assert property ( reset |-> (q == 4'b0000) );

  // Increment by 1 each cycle when not in reset and previous cycle not in reset
  ap_cnt_inc:   assert property ( !reset && !$past(reset) |-> (q == $past(q) + 4'd1) );

  // Coverage: see a wrap-around and a reset event
  cp_cnt_wrap:  cover property ( !reset && $past(!reset) && ($past(q) == 4'hF) && (q == 4'h0) );
  cp_cnt_rst:   cover property ( reset );
endmodule

// Structural assertions for the splitter (combinational equivalence)
module sva_binary_splitter_sv (
  input [2:0] vec,
  input [2:0] outv,
  input o2, o1, o0
);
  // Immediate assertions fire on any combinational change
  always @* begin
    assert (outv === vec) else $error("binary_splitter: outv != vec");
    assert ({o2,o1,o0} === vec) else $error("binary_splitter: {o2,o1,o0} != vec");
  end
endmodule

// Bind statements
bind top_module       sva_control_logic_sv   u_sva_ctrl   (.clk(clk), .reset(reset), .select(select), .vec(vec), .outv(outv), .o2(o2), .o1(o1), .o0(o0));
bind binary_counter   sva_binary_counter_sv  u_sva_cnt    (.clk(clk), .reset(reset), .q(q));
bind binary_splitter  sva_binary_splitter_sv u_sva_split  (.vec(vec), .outv(outv), .o2(o2), .o1(o1), .o0(o0));
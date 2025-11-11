// SVA bind module for magnitude_comparator
module magnitude_comparator_sva (
  input logic       clk,
  input logic [3:0] A, B,
  input logic [3:0] A_reg, B_reg,
  input logic [1:0] stage,
  input logic       out
);
  default clocking cb @(posedge clk); endclocking

  // Guard first cycle for $past usage
  bit started;
  initial started = 1'b0;
  always_ff @(posedge clk) started <= 1'b1;
  default disable iff (!started);

  // Stage must alternate 0 <-> 1, and only use values 0/1
  ap_stage_legal:    assert property ( !( $isunknown(stage) ) |-> (stage inside {2'b00,2'b01}) );
  ap_stage_0_to_1:   assert property ( stage==2'b00 |=> stage==2'b01 );
  ap_stage_1_to_0:   assert property ( stage==2'b01 |=> stage==2'b00 );

  // Capture on stage 0: regs take A/B; Hold on stage 1: regs stable
  ap_capture:        assert property ( stage==2'b00 |=> (A_reg==$past(A) && B_reg==$past(B)) );
  ap_hold_regs:      assert property ( stage==2'b01 |-> ($stable(A_reg) && $stable(B_reg)) );

  // Output updates only after a stage==1 cycle and equals (|A_reg & ~|B_reg)
  ap_out_compute:    assert property ( stage==2'b01 ##1 out == (|A_reg & ~|B_reg) );
  ap_out_only_when:  assert property ( $changed(out) |-> $past(stage)==2'b01 );
  ap_out_stable_s0:  assert property ( stage==2'b00 |-> $stable(out) );
  ap_out_known:      assert property ( $past(stage)==2'b01 |-> !$isunknown(out) );

  // Regs become known after a capture
  ap_regs_known:     assert property ( $past(stage)==2'b00 |-> !$isunknown({A_reg,B_reg}) );

  // Functional cross-check using sampled regs (equivalent form)
  ap_func_truth:     assert property ( $past(stage)==2'b01 |-> out == ($past(|A_reg) & ~$past(|B_reg)) );

  // Coverage
  cp_stage_toggle:   cover  property ( stage==2'b00 ##1 stage==2'b01 ##1 stage==2'b00 );
  cp_out1:           cover  property ( $past(stage)==2'b01 && out==1'b1 );
  cp_out0:           cover  property ( $past(stage)==2'b01 && out==1'b0 );
  cp_both_zero:      cover  property ( stage==2'b01 && (|A_reg)==1'b0 && (|B_reg)==1'b0 );
  cp_both_nonzero:   cover  property ( stage==2'b01 && (|A_reg)==1'b1 && (|B_reg)==1'b1 );
  cp_a0_b1:          cover  property ( stage==2'b01 && (|A_reg)==1'b0 && (|B_reg)==1'b1 );
  cp_a1_b0:          cover  property ( stage==2'b01 && (|A_reg)==1'b1 && (|B_reg)==1'b0 );
endmodule

// Bind into DUT (connects to internal regs as well)
bind magnitude_comparator magnitude_comparator_sva mc_sva (
  .clk   (clk),
  .A     (A),
  .B     (B),
  .A_reg (A_reg),
  .B_reg (B_reg),
  .stage (stage),
  .out   (out)
);
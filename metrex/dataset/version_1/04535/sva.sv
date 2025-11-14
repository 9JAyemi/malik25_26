// SVA for flip_flop. Bind this to the DUT.
module flip_flop_sva (
  input logic Q,
  input logic CLK,
  input logic D,
  input logic SCD,
  input logic SCE,
  input logic RESET_B
);
  default clocking cb @ (posedge CLK); endclocking

  // Asynchronous reset behavior (checked at synchronous edges)
  // Q must be 0 whenever reset is low, and around reset edges.
  a_rst_low_holds_q0:    assert property (@(posedge CLK) !RESET_B |-> (Q==1'b0));
  a_rst_assert_seen:     assert property (@(posedge CLK) $fell(RESET_B) |-> (Q==1'b0));
  a_rst_release_hold0:   assert property (@(posedge CLK) $rose(RESET_B) |-> (Q==1'b0));

  // Priority and synchronous update on CLK
  a_scd_sets1:           assert property (disable iff (!RESET_B) SCD |=> (Q==1'b1));
  a_sce_clears0:         assert property (disable iff (!RESET_B) (SCE && !SCD) |=> (Q==1'b0));
  a_d_path:              assert property (disable iff (!RESET_B) (!SCD && !SCE) |=> (Q==D));
  a_tie_pref_scd:        assert property (disable iff (!RESET_B) (SCD && SCE) |=> (Q==1'b1)); // explicit priority check

  // X checks (optional but recommended)
  a_inputs_known:        assert property (@(posedge CLK) RESET_B |-> !$isunknown({SCD,SCE,D}));
  a_q_known:             assert property (@(posedge CLK) !$isunknown(Q));

  // Functional coverage
  c_reset_assert:        cover  property (@(posedge CLK) $fell(RESET_B));
  c_reset_release:       cover  property (@(posedge CLK) $rose(RESET_B));
  c_scd_path:            cover  property (disable iff (!RESET_B) SCD ##1 (Q==1));
  c_sce_path:            cover  property (disable iff (!RESET_B) (!SCD && SCE) ##1 (Q==0));
  c_d_path:              cover  property (disable iff (!RESET_B) (!SCD && !SCE) ##1 (Q==D));
  c_tie_priority:        cover  property (disable iff (!RESET_B) (SCD && SCE) ##1 (Q==1));
  c_q_rose:              cover  property (disable iff (!RESET_B) $rose(Q));
  c_q_fell:              cover  property (disable iff (!RESET_B) $fell(Q));
endmodule

bind flip_flop flip_flop_sva sva_ff_i (
  .Q(Q), .CLK(CLK), .D(D), .SCD(SCD), .SCE(SCE), .RESET_B(RESET_B)
);
// SVA for power_supply
module power_supply_sva (
  input clk,
  input rst,
  input VPWR,
  input VGND,
  input VPB,
  input VNB
);

  default clocking cb @ (posedge clk); endclocking

  // Known, legal states only
  a_known:        assert property (@cb !$isunknown({VPWR,VGND,VPB,VNB}));
  a_legal_states: assert property (@cb {VPWR,VGND,VPB,VNB} inside {4'b0000, 4'b1010});

  // While in reset, all rails low
  a_rst_zeros:    assert property (@cb rst |-> {VPWR,VGND,VPB,VNB} == 4'b0000);

  // Out of reset, steady active rails: VPWR/VPB=1, VGND/VNB=0
  a_active_vals:  assert property (@cb !rst |-> {VPWR,VGND,VPB,VNB} == 4'b1010);

  // Optional: simple pair consistency (redundant with legal_states but explicit)
  a_pair_consist1: assert property (@cb VPWR == VPB);
  a_pair_consist2: assert property (@cb VGND == VNB);

  // Coverage
  c_reset_state:   cover property (@cb {VPWR,VGND,VPB,VNB} == 4'b0000);
  c_active_state:  cover property (@cb {VPWR,VGND,VPB,VNB} == 4'b1010);
  c_reset_cycle:   cover property (@cb $rose(rst) ##[1:$] $fell(rst) ##1 ({VPWR,VGND,VPB,VNB} == 4'b1010));

endmodule

// Bind into DUT
bind power_supply power_supply_sva sva_i (
  .clk (clk),
  .rst (rst),
  .VPWR(VPWR),
  .VGND(VGND),
  .VPB (VPB),
  .VNB (VNB)
);
// SVA for power_supply: concise, high-quality checks and coverage
module power_supply_sva (
  input  logic       clk,
  input  logic [1:0] state,
  input  logic       VPB,
  input  logic       VNB
);
  default clocking cb @(posedge clk); endclocking

  // Output mapping per state
  ap_map_hi: assert property (disable iff ($isunknown(state))
                              (state inside {2'b00,2'b10}) |-> (VPB === 1'b1 && VNB === 1'b0))
    else $error("VPB/VNB wrong for state 00/10");

  ap_map_lo: assert property (disable iff ($isunknown(state))
                              (state inside {2'b01,2'b11}) |-> (VPB === 1'b0 && VNB === 1'b1))
    else $error("VPB/VNB wrong for state 01/11");

  // Outputs always complementary (and known)
  ap_compl: assert property (!$isunknown({VPB,VNB}) |-> (VPB == ~VNB))
    else $error("VPB and VNB not complementary");

  // State increments by +1 mod-4 every cycle once known
  ap_inc: assert property (!$isunknown($past(state)) |-> state == ($past(state) + 2'd1))
    else $error("State did not increment mod-4");

  // Outputs toggle every cycle
  ap_vpb_tog: assert property (!$isunknown($past(VPB)) |-> VPB != $past(VPB))
    else $error("VPB did not toggle");
  ap_vnb_tog: assert property (!$isunknown($past(VNB)) |-> VNB != $past(VNB))
    else $error("VNB did not toggle");

  // Periodicity
  ap_state_period4: assert property (!$isunknown($past(state,4)) |-> state == $past(state,4))
    else $error("State not 4-cycle periodic");
  ap_vpb_period2:  assert property (!$isunknown($past(VPB,2))  |-> VPB  == $past(VPB,2))
    else $error("VPB not 2-cycle periodic");
  ap_vnb_period2:  assert property (!$isunknown($past(VNB,2))  |-> VNB  == $past(VNB,2))
    else $error("VNB not 2-cycle periodic");

  // Coverage: full state round and output alternation
  cp_full_round:  cover property (state == 2'b00 ##1 state == 2'b01 ##1 state == 2'b10 ##1 state == 2'b11 ##1 state == 2'b00);
  cp_outputs_alt: cover property (VPB && !VNB ##1 !VPB && VNB ##1 VPB && !VNB);
endmodule

bind power_supply power_supply_sva u_power_supply_sva (.clk(clk), .state(state), .VPB(VPB), .VNB(VNB));
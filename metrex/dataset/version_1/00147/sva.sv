// SVA for dff_sr
module dff_sr_sva (
  input logic Q,
  input logic Q_N,
  input logic D,
  input logic CLK,
  input logic SET_B,
  input logic RESET_B
);
  default clocking cb @(posedge CLK); endclocking

  // Combinational invariant
  ap_qn_compl: assert property (Q_N === ~Q);

  // Sequential behavior on each posedge based on previous-cycle controls
  ap_set_only:   assert property ($past(~SET_B &  RESET_B) |-> (Q == 1'b1));
  ap_reset_only: assert property ($past( SET_B & ~RESET_B) |-> (Q == 1'b0));
  ap_both_low_d: assert property (($past(~SET_B & ~RESET_B) && !$isunknown($past(D))) |-> (Q == $past(D)));
  ap_hold:       assert property ($past( SET_B &  RESET_B) |-> (Q === $past(Q)));

  // Coverage
  cp_set_only:   cover property (~SET_B &  RESET_B);
  cp_reset_only: cover property ( SET_B & ~RESET_B);
  cp_both_low:   cover property (~SET_B & ~RESET_B);
  cp_hold:       cover property ( SET_B &  RESET_B);
  cp_q_rise:     cover property ($past(Q)==1'b0 && Q==1'b1);
  cp_q_fall:     cover property ($past(Q)==1'b1 && Q==1'b0);
  cp_data_cap:   cover property ($past(~SET_B & ~RESET_B & !$isunknown(D)) && (Q == $past(D)));
endmodule

bind dff_sr dff_sr_sva dff_sr_sva_i(.Q(Q), .Q_N(Q_N), .D(D), .CLK(CLK), .SET_B(SET_B), .RESET_B(RESET_B));
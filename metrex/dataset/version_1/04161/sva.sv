// SVA for up_down_counter
// Bind this checker to the DUT:  bind up_down_counter up_down_counter_sva u_updn_sva (.*);

module up_down_counter_sva (
  input logic       CLK,
  input logic       RST,
  input logic       LD,
  input logic       UD,
  input logic [3:0] D,
  input logic [3:0] Q
);
  default clocking cb @(posedge CLK); endclocking

  // Track availability of $past()
  bit past_valid;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Basic X checks
  ap_ctrl_known:   assert property (cb !$isunknown({RST,LD,UD}));
  ap_data_known:   assert property (cb LD |-> !$isunknown(D));
  ap_out_known:    assert property (cb !$isunknown({Q,Q_reg1,Q_reg2}));

  // Output wiring
  ap_q_maps_q1:    assert property (cb Q == Q_reg1);

  // Reset and load behavior (Q)
  ap_rst_q:        assert property (cb RST |=> Q == 4'h0);
  ap_ld_q:         assert property (cb !RST && LD |=> Q == D);

  // Priority: LD over UD
  ap_ld_over_ud:   assert property (cb !RST && LD && UD |=> Q == D);

  // Counting behavior (uses Q_reg2 as the operand)
  ap_up:           assert property (cb past_valid && !RST && !LD && UD  |=> Q == ($past(Q_reg2) + 4'h1));
  ap_down:         assert property (cb past_valid && !RST && !LD && !UD |=> Q == ($past(Q_reg2) - 4'h1));

  // Pipeline relation: Q_reg2 is one-cycle delayed Q_reg1
  ap_q2_delays_q1: assert property (cb past_valid |-> Q_reg2 == $past(Q_reg1));

  // Intended synchronous mirror on RST/LD (flags the last-NBA overwrite bug if present)
  ap_q2_matches_q_on_rst_or_ld: assert property (cb (RST || LD) |=> Q_reg2 == Q);

  // Wrap-around functional checks
  ap_wrap_up:      assert property (cb past_valid && !RST && !LD && UD  && $past(Q_reg2)==4'hF |=> Q==4'h0);
  ap_wrap_down:    assert property (cb past_valid && !RST && !LD && !UD && $past(Q_reg2)==4'h0 |=> Q==4'hF);

  // Functional coverage
  cp_rst:          cover property (cb RST ##1 Q==4'h0);
  cp_ld:           cover property (cb !RST && LD ##1 Q==D);
  cp_up:           cover property (cb !RST && !LD && UD);
  cp_down:         cover property (cb !RST && !LD && !UD);
  cp_wrap_up:      cover property (cb !RST && !LD && UD  && Q_reg2==4'hF ##1 Q==4'h0);
  cp_wrap_down:    cover property (cb !RST && !LD && !UD && Q_reg2==4'h0 ##1 Q==4'hF);
  cp_ld_ud_both:   cover property (cb !RST && LD && UD ##1 Q==D);
  cp_seq:          cover property (cb RST ##1 !RST && LD ##1 !LD && UD ##1 !LD && !UD);
endmodule

bind up_down_counter up_down_counter_sva u_updn_sva (.*);
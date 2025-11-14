// SVA for robotic_arm_controller
module robotic_arm_controller_sva (
  input  logic        clk,
  input  logic        btn,
  input  logic  [1:0] pos,
  input  logic        X
);
  default clocking cb @(posedge clk); endclocking

  // Skip $past checks on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z on key signals (after first cycle)
  a_knowns: assert property (past_valid |-> !$isunknown({btn,pos,X}));

  // State space invariant: never reach 2'b11
  a_pos_range: assert property (past_valid |-> pos != 2'b11);

  // Combinational output mapping
  a_X_maps_pos0: assert property (X == pos[0]);

  // Exact next-state function
  a_next_state: assert property (
    past_valid |->
      pos == ( $past(btn)
               ? ( ($past(pos)==2'b10) ? 2'b00 : $past(pos)+2'b01 )
               : $past(pos) )
  );

  // Optional stability when btn was low (redundant with a_next_state but clearer failure)
  a_hold_when_btn0: assert property (past_valid && !$past(btn) |-> pos == $past(pos));

  // Coverage: hit all legal states
  c_pos_00: cover property (past_valid && pos==2'b00);
  c_pos_01: cover property (past_valid && pos==2'b01);
  c_pos_10: cover property (past_valid && pos==2'b10);

  // Coverage: full 00->01->10->00 cycle
  c_full_cycle: cover property (
    past_valid && pos==2'b00 ##1 pos==2'b01 ##1 pos==2'b10 ##1 pos==2'b00
  );

  // Coverage: demonstrate a hold when btn is low
  c_hold: cover property (past_valid && !$past(btn) && pos==$past(pos));
endmodule

// Bind into DUT (connects internal pos)
bind robotic_arm_controller robotic_arm_controller_sva sva_i (
  .clk(clk),
  .btn(btn),
  .pos(pos),
  .X  (X)
);
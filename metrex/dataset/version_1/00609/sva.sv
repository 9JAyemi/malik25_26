// SVA for module complement
// Bind file

module complement_sva (
  input logic CLK,
  input logic D,
  input logic Q,
  input logic reg1,
  input logic reg2
);

  default clocking @(posedge CLK); endclocking

  logic past_valid, past2_valid;
  initial begin past_valid = 1'b0; past2_valid = 1'b0; end
  always_ff @(posedge CLK) begin
    past2_valid <= past_valid;
    past_valid  <= 1'b1;
  end

  // Functional correctness of the D→reg1→Q pipeline
  a_reg1_tracks_D:  assert property (past_valid  |-> reg1 == $past(D));
  a_Q_tracks_reg1:  assert property (past_valid  |-> Q    == $past(reg1));
  a_Q_tracks_D2:    assert property (past2_valid |-> Q    == $past(D,2));

  // Sanity: no X on observable flops once pipeline has at least 1 cycle history
  a_no_x_regs:      assert property (past_valid |-> !$isunknown({reg1,Q}));

  // reg2 has two NBAs in the same clock (race). Constrain observable outcomes and cover both.
  a_reg2_outcomes:  assert property (past_valid |-> (reg2 == $past(reg1)) || (reg2 == ~$past(reg2)));
  c_reg2_follow:    cover  property (past_valid && (reg2 == $past(reg1)));
  c_reg2_toggle:    cover  property (past_valid && (reg2 == ~$past(reg2)));

  // Coverage for D→Q behavior
  c_D_rise_Q_high_2c: cover property (past2_valid && $rose(D) ##2 Q);
  c_D_fall_Q_low_2c:  cover property (past2_valid && $fell(D) ##2 !Q);
  c_Q_toggles:        cover property (past_valid && $changed(Q));

endmodule

bind complement complement_sva sva_i (.*);
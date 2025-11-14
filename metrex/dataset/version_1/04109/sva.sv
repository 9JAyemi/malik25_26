// SVA for binary_storage_shift
// Bind into the DUT to access internals.
module binary_storage_shift_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d,
  input  logic [1:0]  shift_ctrl,
  input  logic [7:0]  q,
  input  logic [7:0]  q_shifted,
  input  logic [3:0]  flip_flop,
  input  logic [7:0]  shifted_d,
  input  logic [1:0]  shift_amt
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (sync active-high)
  a_reset_regs_zero: assert property (reset |-> (q == 8'h00 && q_shifted == 8'h00 && flip_flop == 4'h0));

  // Combinational decode: shift_amt mirrors shift_ctrl
  a_shift_amt_id:    assert property (shift_amt == shift_ctrl);

  // flip_flop next-state function
  a_ff_next:         assert property (!reset |-> flip_flop == {$past(flip_flop[2:0]), d[7]});

  // q captures previous flip_flop (zero-extended into 8 bits)
  a_q_mapping:       assert property (!reset |-> q == {4'b0000, $past(flip_flop)});

  // shifted_d update each cycle (no reset intended in DUT)
  a_shifted_d_upd:   assert property (!reset |-> shifted_d == {d[5:0], 2'b00});

  // q_shifted uses previous shifted_d and current shift_amt (skip first cycle after reset)
  a_q_shifted_fn:    assert property (!reset && !$past(reset) |-> q_shifted == ($past({d[5:0],2'b00}) << shift_ctrl));

  // Known-value checks (avoid X/Z propagation)
  a_known_q:         assert property (!reset |-> !$isunknown(q));
  a_known_ff:        assert property (!reset |-> !$isunknown(flip_flop));
  a_known_sd:        assert property (!reset |-> !$isunknown(shifted_d));
  a_known_qs:        assert property (!reset && !$past(reset) |-> !$isunknown(q_shifted));

  // Minimal functional coverage
  c_reset_release:   cover property (reset ##1 !reset);
  c_shift_00:        cover property (!reset && !$past(reset) && shift_ctrl == 2'b00);
  c_shift_01:        cover property (!reset && !$past(reset) && shift_ctrl == 2'b01);
  c_shift_10:        cover property (!reset && !$past(reset) && shift_ctrl == 2'b10);
  c_shift_11:        cover property (!reset && !$past(reset) && shift_ctrl == 2'b11);
  c_d7_low:          cover property (!reset && d[7] == 1'b0);
  c_d7_high:         cover property (!reset && d[7] == 1'b1);
  c_q_changes:       cover property (!reset && q != $past(q));
  c_qs_changes:      cover property (!reset && !$past(reset) && q_shifted != $past(q_shifted));

endmodule

bind binary_storage_shift binary_storage_shift_sva sva_i (
  .clk       (clk),
  .reset     (reset),
  .d         (d),
  .shift_ctrl(shift_ctrl),
  .q         (q),
  .q_shifted (q_shifted),
  .flip_flop (flip_flop),
  .shifted_d (shifted_d),
  .shift_amt (shift_amt)
);
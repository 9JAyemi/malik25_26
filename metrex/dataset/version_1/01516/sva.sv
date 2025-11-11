// SVA for jt12_single_acc
// Bind these assertions into the DUT

bind jt12_single_acc jt12_single_acc_sva #(.WIN(win), .WOUT(wout)) i_jt12_single_acc_sva (
  .clk(clk),
  .clk_en(clk_en),
  .op_result(op_result),
  .sum_en(sum_en),
  .zero(zero),
  .snd(snd),
  .acc(acc),
  .current(current),
  .next(next),
  .overflow(overflow)
);

module jt12_single_acc_sva #(parameter int WIN=14, WOUT=16) (
  input  logic                 clk,
  input  logic                 clk_en,
  input  logic [WIN-1:0]       op_result,
  input  logic                 sum_en,
  input  logic                 zero,
  input  logic [WOUT-1:0]      snd,
  input  logic signed [WOUT-1:0] acc,
  input  logic signed [WOUT-1:0] current,
  input  logic signed [WOUT-1:0] next,
  input  logic                 overflow
);

  localparam logic [WOUT-1:0] PLUS_INF  = {1'b0, {(WOUT-1){1'b1}}};
  localparam logic [WOUT-1:0] MINUS_INF = {1'b1, {(WOUT-1){1'b0}}};

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  initial assert (WOUT >= WIN) else $fatal(1, "jt12_single_acc: wout < win");

  default clocking cb @(posedge clk); endclocking

  // Combinational invariants
  a_current_se_1: assert property (sum_en |-> current == { {(WOUT-WIN){op_result[WIN-1]}}, op_result });
  a_current_se_0: assert property (!sum_en |-> current == {WOUT{1'b0}});
  a_next_zero:    assert property (zero |-> next == current);
  a_next_add:     assert property (!zero |-> next == $signed(current) + $signed(acc));

  // Overflow definition (two's complement add overflow) and constraints
  a_ovf_implies:  assert property (overflow |-> (!zero && (current[WOUT-1]==acc[WOUT-1]) && (acc[WOUT-1]!=next[WOUT-1])));
  a_ovf_iff_dir:  assert property ((!zero && (current[WOUT-1]==acc[WOUT-1]) && (acc[WOUT-1]!=next[WOUT-1])) |-> overflow);
  a_ovf_not_on_zero: assert property (overflow |-> !zero);

  // Hold when clk_en deasserted
  a_hold_no_en: assert property (past_valid && !$past(clk_en) |-> acc == $past(acc) && snd == $past(snd));

  // Sequential acc update rules
  a_acc_sat_pos: assert property (past_valid && $past(clk_en) && $past(overflow) && !$past(acc[WOUT-1]) |-> acc == PLUS_INF);
  a_acc_sat_neg: assert property (past_valid && $past(clk_en) && $past(overflow) &&  $past(acc[WOUT-1]) |-> acc == MINUS_INF);
  a_acc_no_ovf:  assert property (past_valid && $past(clk_en) && !$past(overflow) |-> acc == $past(next));

  // snd update rule (snd captures previous acc only when zero)
  a_snd_on_zero:  assert property (past_valid && $past(clk_en) && $past(zero)   |-> snd == $past(acc));
  a_snd_hold_nz:  assert property (past_valid && $past(clk_en) && !$past(zero) |-> snd == $past(snd));

  // Coverage
  c_pos_sat: cover property (past_valid && $past(clk_en) && $past(overflow) && !$past(acc[WOUT-1]) && acc == PLUS_INF);
  c_neg_sat: cover property (past_valid && $past(clk_en) && $past(overflow) &&  $past(acc[WOUT-1]) && acc == MINUS_INF);
  c_no_ovf:   cover property (past_valid && $past(clk_en) && !$past(overflow) && acc == $past(next));
  c_zero_path: cover property (past_valid && $past(clk_en) && $past(zero) && snd == $past(acc));
  c_sum_en0:  cover property (!sum_en && current == {WOUT{1'b0}});
  c_sum_en1_msb0: cover property (sum_en && !op_result[WIN-1] && current == { {(WOUT-WIN){1'b0}}, op_result });
  c_sum_en1_msb1: cover property (sum_en &&  op_result[WIN-1] && current == { {(WOUT-WIN){1'b1}}, op_result });

endmodule
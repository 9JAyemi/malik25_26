// SVA for jt12_eg_cnt
// Bind into DUT to access internal eg_cnt_base

module jt12_eg_cnt_sva_bind(
  input  logic        rst,
  input  logic        clk,
  input  logic        clk_en,
  input  logic        zero,
  input  logic [14:0] eg_cnt,
  input  logic [1:0]  eg_cnt_base
);

  // helper: one-cycle-after-reset valid for $past/$stable use
  logic past_valid;
  always @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  wire gate = zero && clk_en;

  // Asynchronous reset behavior
  // Immediate clear on posedge rst
  assert property (@(posedge rst) (eg_cnt == 15'd0 && eg_cnt_base == 2'd0));
  // Hold at zero while rst is asserted
  assert property (@(posedge clk) rst |-> (eg_cnt == 15'd0 && eg_cnt_base == 2'd0));

  // State-space constraint: base never 3
  assert property (eg_cnt_base inside {2'd0,2'd1,2'd2});

  // No state change when gate is low
  assert property (past_valid && !gate |=> $stable(eg_cnt) && $stable(eg_cnt_base));

  // Base counting rules when gate is high
  // 0 -> 1, eg_cnt holds
  assert property (past_valid && gate && eg_cnt_base == 2'd0
                   |=> eg_cnt_base == 2'd1 && $stable(eg_cnt));
  // 1 -> 2, eg_cnt holds
  assert property (past_valid && gate && eg_cnt_base == 2'd1
                   |=> eg_cnt_base == 2'd2 && $stable(eg_cnt));
  // 2 -> 0 and eg_cnt increments by 1 (mod 2^15)
  assert property (past_valid && gate && eg_cnt_base == 2'd2
                   |=> eg_cnt_base == 2'd0 && eg_cnt == $past(eg_cnt)+15'd1);

  // eg_cnt can only change as a +1 increment, and only on the 2->0 event
  assert property (past_valid && $changed(eg_cnt)
                   |-> eg_cnt == $past(eg_cnt)+15'd1 && $past(gate && eg_cnt_base==2'd2));

  // Outputs/regs known (no X/Z) after reset release
  assert property (past_valid |-> !$isunknown({eg_cnt, eg_cnt_base}));

  // Coverage
  // Observe one full 0->1->2->0 cycle with an eg_cnt increment
  sequence three_gated_steps;
    gate && eg_cnt_base==2'd0 ##1
    gate && eg_cnt_base==2'd1 ##1
    gate && eg_cnt_base==2'd2;
  endsequence
  cover property (past_valid && three_gated_steps ##1 (eg_cnt_base==2'd0 && eg_cnt == $past(eg_cnt,1)+15'd1));

  // See gating inactive then active
  cover property (past_valid && !gate ##1 gate);

endmodule

bind jt12_eg_cnt jt12_eg_cnt_sva_bind
  i_jt12_eg_cnt_sva_bind(
    .rst(rst),
    .clk(clk),
    .clk_en(clk_en),
    .zero(zero),
    .eg_cnt(eg_cnt),
    .eg_cnt_base(eg_cnt_base)
  );
// SVA for pace_catcher
// Focused, concise checks and coverage across both clock domains.

module pace_catcher_sva #(
  parameter int COUNT  = 15,
  parameter bit S_IDLE = 1'b0,
  parameter bit S_OUT  = 1'b1
)(
  input logic              clk_fast,
  input logic              clk_slow,
  input logic              signal_i,
  input logic              signal_o,
  input logic [15:0]       cnt,
  input logic              state
);

  // past-valid flags per clock to avoid first-cycle $past issues
  logic fast_pv, slow_pv;
  initial begin fast_pv = 1'b0; slow_pv = 1'b0; end
  always @(posedge clk_fast) fast_pv <= 1'b1;
  always @(posedge clk_slow) slow_pv <= 1'b1;

  // Basic sanity: no X/Z on key signals
  assert property (@(posedge clk_fast) !$isunknown({state, signal_o, signal_i}));
  assert property (@(posedge clk_slow) !$isunknown(cnt));

  // Output reflects state encoding
  assert property (@(posedge clk_fast) disable iff (!fast_pv)
                   signal_o == (state == S_OUT));

  // State machine transition checks (clk_fast domain)
  // Idle behavior
  assert property (@(posedge clk_fast) disable iff (!fast_pv)
                   (state == S_IDLE && !signal_i) |=> (state == S_IDLE));
  assert property (@(posedge clk_fast) disable iff (!fast_pv)
                   (state == S_IDLE &&  signal_i) |=> (state == S_OUT));

  // Out behavior: hold until COUNT, then exit
  assert property (@(posedge clk_fast) disable iff (!fast_pv)
                   (state == S_OUT && (cnt < COUNT))  |=> (state == S_OUT));
  assert property (@(posedge clk_fast) disable iff (!fast_pv)
                   (state == S_OUT && (cnt >= COUNT)) |=> (state == S_IDLE));

  // Counter behavior (clk_slow domain)
  // Increment by 1 while OUT; 0 while IDLE
  assert property (@(posedge clk_slow) disable iff (!slow_pv)
                   (state == S_OUT)  |=> (cnt == $past(cnt) + 16'd1));
  assert property (@(posedge clk_slow) disable iff (!slow_pv)
                   (state == S_IDLE) |=> (cnt == 16'd0));

  // On the first slow edge after leaving OUT, counter must be 0
  assert property (@(posedge clk_slow) disable iff (!slow_pv)
                   ($past(state) == S_OUT && state == S_IDLE) |-> (cnt == 16'd0));

  // Cross-domain consistency: if COUNT reached while OUT, next fast edge exits
  assert property (@(posedge clk_fast) disable iff (!fast_pv)
                   (state == S_OUT && cnt >= COUNT) |=> (state == S_IDLE));

  // Coverage
  // 1) Observe an activate sequence and eventual deassert
  cover property (@(posedge clk_fast)
                  (state == S_IDLE && signal_i) ##1
                  (state == S_OUT) ##[1:$]
                  (state == S_OUT && cnt >= COUNT) ##1
                  (state == S_IDLE));

  // 2) See cnt count up to COUNT in OUT state (clk_slow perspective)
  cover property (@(posedge clk_slow) disable iff (!slow_pv)
                  (state == S_OUT && cnt == 16'd0) ##[1:COUNT]
                  (state == S_OUT && cnt == COUNT));

  // 3) Simple toggle coverage: Idle->Out and Out->Idle
  cover property (@(posedge clk_fast) (state == S_IDLE && signal_i) ##1 (state == S_OUT));
  cover property (@(posedge clk_fast) (state == S_OUT && cnt >= COUNT) ##1 (state == S_IDLE));

endmodule

// Bind into DUT; connects to internal state and cnt
bind pace_catcher
  pace_catcher_sva #(.COUNT(COUNT), .S_IDLE(s_idle), .S_OUT(s_out))
  pace_catcher_sva_i (
    .clk_fast (clk_fast),
    .clk_slow (clk_slow),
    .signal_i (signal_i),
    .signal_o (signal_o),
    .cnt      (cnt),
    .state    (state)
  );
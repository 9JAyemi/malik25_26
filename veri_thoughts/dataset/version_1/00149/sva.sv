// SVA for subtractor
// Bindable, concise, and checks key behaviors

module subtractor_sva (
  input logic         wr_clk,
  input logic         AR,
  input logic [8:0]   count_d2_reg,
  input logic [3:0]   S,
  input logic [9:0]   wr_data_count
);

  // Golden model (matches DUT widths/truncation)
  logic [3:0] exp_const;
  logic [8:0] exp_sub;
  logic [9:0] exp_out;

  assign exp_const = (10 - ($unsigned(S) * 10)) & 4'hF; // 4-bit wrap
  assign exp_sub   = $unsigned(count_d2_reg) - $unsigned(exp_const);
  assign exp_out   = {1'b0, exp_sub};

  // Async reset drives 0 immediately at negedge AR
  a_async_reset_immediate: assert property (@(negedge AR) 1 |-> ##0 (wr_data_count == 10'd0));

  // While in reset on clock edges, hold 0
  a_reset_hold_zero:       assert property (@(posedge wr_clk) !AR |-> (wr_data_count == 10'd0));

  // Functional correctness on each active clock
  a_update_correct:        assert property (@(posedge wr_clk) AR |-> (wr_data_count == exp_out));

  // MSB must always be 0 (by design concatenation)
  a_msb_zero:              assert property (@(posedge wr_clk) (wr_data_count[9] == 1'b0));

  // No X/Z when active
  a_no_x_active:           assert property (@(posedge wr_clk) AR |-> !$isunknown({S, count_d2_reg, wr_data_count}));

  // Stability: if inputs stable and AR high, output stable across cycles
  a_stable_when_inputs_stable: assert property (@(posedge wr_clk)
                                  AR && $stable({count_d2_reg, S}) |-> $stable(wr_data_count));

  // Coverage

  // Reset pulse observed
  c_reset_pulse:           cover property (@(posedge wr_clk) $fell(AR) ##[1:$] $rose(AR));

  // Exercise representative S cases, incl. wrap behavior
  c_s0:                    cover property (@(posedge wr_clk) AR && (S == 4'd0));
  c_s1:                    cover property (@(posedge wr_clk) AR && (S == 4'd1));
  c_s2_wrap:               cover property (@(posedge wr_clk) AR && (S == 4'd2));    // 10-20 -> wrap to 6
  c_s15_wrap:              cover property (@(posedge wr_clk) AR && (S == 4'd15));   // 10-150 -> wrap

  // Underflow vs non-underflow in subtraction
  c_no_underflow:          cover property (@(posedge wr_clk) AR && (count_d2_reg >= exp_const));
  c_underflow:             cover property (@(posedge wr_clk) AR && (count_d2_reg <  exp_const));

  // Extremes of count
  c_min_count:             cover property (@(posedge wr_clk) AR && (count_d2_reg == 9'd0));
  c_max_count:             cover property (@(posedge wr_clk) AR && (count_d2_reg == 9'd511));

  // Output activity
  c_output_changes:        cover property (@(posedge wr_clk) AR && $changed(wr_data_count));

endmodule

// Bind into the DUT
bind subtractor subtractor_sva sva_inst (.*);
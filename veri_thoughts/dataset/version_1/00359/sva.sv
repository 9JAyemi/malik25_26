// SVA for Freq_Count_Top
// Bind-friendly, references internal DUT signals via ports.
module Freq_Count_Top_sva (
  input  logic        sys_clk_50m,
  input  logic        ch_c,
  input  logic        sys_rst_n,

  input  logic [31:0] count,
  input  logic        Gate_1S,
  input  logic        EN_FT,
  input  logic        CLR,
  input  logic [63:0] FT_out,
  input  logic        Load,
  input  logic [63:0] freq_reg,

  input  logic [31:0] HIGH_TIME_Gate_1S,
  input  logic [31:0] LOW_TIME_Gate_1S
);

  // Parameter sanity
  initial begin
    assert (LOW_TIME_Gate_1S > HIGH_TIME_Gate_1S && HIGH_TIME_Gate_1S > 0)
      else $error("Illegal HIGH/LOW time parameters");
  end

  // Reset behavior (sys clock domain)
  assert property (@(posedge sys_clk_50m or negedge sys_rst_n)
                   !sys_rst_n |-> (count==32'd0 && Gate_1S==1'b0));

  // count progression and wrap
  assert property (@(posedge sys_clk_50m)
                   disable iff (!sys_rst_n)
                   $past(sys_rst_n) && ($past(count) != LOW_TIME_Gate_1S)
                   |-> count == $past(count)+1);

  assert property (@(posedge sys_clk_50m)
                   disable iff (!sys_rst_n)
                   $past(sys_rst_n) && ($past(count) == LOW_TIME_Gate_1S)
                   |-> (count==32'd1 && Gate_1S));

  // Gate level vs count range
  assert property (@(posedge sys_clk_50m)
                   disable iff (!sys_rst_n)
                   (count>32'd0 && count<HIGH_TIME_Gate_1S) |-> Gate_1S);

  assert property (@(posedge sys_clk_50m)
                   disable iff (!sys_rst_n)
                   (count>HIGH_TIME_Gate_1S && count<LOW_TIME_Gate_1S) |-> !Gate_1S);

  // Gate transitions only at thresholds
  assert property (@(posedge sys_clk_50m)
                   disable iff (!sys_rst_n)
                   $rose(Gate_1S) |-> $past(count)==LOW_TIME_Gate_1S);

  assert property (@(posedge sys_clk_50m)
                   disable iff (!sys_rst_n)
                   $fell(Gate_1S) |-> $past(count)==HIGH_TIME_Gate_1S);

  // ch_c domain: reset for EN_FT
  assert property (@(posedge ch_c or negedge sys_rst_n)
                   !sys_rst_n |-> EN_FT==1'b0);

  // EN_FT samples Gate_1S on ch_c edge
  assert property (@(posedge ch_c)
                   disable iff (!sys_rst_n)
                   EN_FT == Gate_1S);

  // Load is complement of EN_FT and edges correlate
  assert property (@(posedge ch_c) Load == ~EN_FT);
  assert property (@(posedge ch_c) disable iff (!sys_rst_n) $rose(Load) |-> $fell(EN_FT));
  assert property (@(posedge ch_c) disable iff (!sys_rst_n) $fell(EN_FT) |-> $rose(Load));

  // CLR updates to (Gate_1S | EN_FT) on each ch_c edge (check previous-cycle assignment)
  assert property (@(posedge ch_c)
                   disable iff (!sys_rst_n)
                   $past(CLR) == ($past(Gate_1S) || $past(EN_FT)));

  // Asynchronous clear behavior on FT_out
  assert property (@(negedge CLR) FT_out==64'd0);

  // FT_out increments when enabled, holds otherwise (prior to clear)
  assert property (@(posedge ch_c)
                   disable iff (!sys_rst_n)
                   (EN_FT && $past(CLR)) |=> FT_out == $past(FT_out)+1);

  assert property (@(posedge ch_c)
                   disable iff (!sys_rst_n)
                   (!EN_FT && $past(CLR)) |=> FT_out == $past(FT_out));

  // While counting window open, freq_reg must stay stable
  assert property (@(posedge ch_c)
                   disable iff (!sys_rst_n)
                   EN_FT |-> $stable(freq_reg));

  // Capture: when EN_FT falls (Load rises), next ch_c edge sees freq_reg latched to last FT_out
  assert property (@(posedge ch_c)
                   disable iff (!sys_rst_n)
                   $fell(EN_FT) |=> freq_reg == $past(FT_out));

  // ------------- Coverage -------------

  // Hit both thresholds
  cover property (@(posedge sys_clk_50m) count==HIGH_TIME_Gate_1S && !Gate_1S);
  cover property (@(posedge sys_clk_50m) count==LOW_TIME_Gate_1S  &&  Gate_1S);

  // Observe a full measurement: enable -> count some pulses -> capture non-zero
  cover property (@(posedge ch_c)
    disable iff (!sys_rst_n)
    $rose(EN_FT) ##[1:$] (FT_out>0) ##[1:$] $fell(EN_FT) ##1 (freq_reg==$past(FT_out)));

  // Reach a reasonably large FT_out value (e.g., >100 pulses) within a window
  cover property (@(posedge ch_c) disable iff (!sys_rst_n) FT_out >= 64'd100);

endmodule

// Bind into DUT
bind Freq_Count_Top Freq_Count_Top_sva sva_i (
  .sys_clk_50m(sys_clk_50m),
  .ch_c(ch_c),
  .sys_rst_n(sys_rst_n),

  .count(count),
  .Gate_1S(Gate_1S),
  .EN_FT(EN_FT),
  .CLR(CLR),
  .FT_out(FT_out),
  .Load(Load),
  .freq_reg(freq_reg),

  .HIGH_TIME_Gate_1S(HIGH_TIME_Gate_1S),
  .LOW_TIME_Gate_1S(LOW_TIME_Gate_1S)
);
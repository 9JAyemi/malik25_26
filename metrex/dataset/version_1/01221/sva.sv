// SVA for debounce_switch
// Bind this module to the DUT: bind debounce_switch debounce_switch_sva #(.WIDTH(WIDTH), .N(N), .RATE(RATE)) sva (.*);

module debounce_switch_sva #(parameter int WIDTH=1, N=3, RATE=125000);

  // Access DUT scope via bind (assumes same names)
  logic clk, rst;
  logic [WIDTH-1:0] in, out;
  logic [23:0] cnt_reg;
  logic [WIDTH-1:0] state;
  logic [N-1:0] debounce_reg [WIDTH-1:0];

  // Default clock and reset for assertions
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helper
  logic tick;
  assign tick = (cnt_reg==24'd0);

  // Reset behavior (asynchronous reset observed on clock)
  assert property (@(posedge clk) rst |-> (cnt_reg==24'd0 && state=='0 && (foreach (state[k]) (debounce_reg[k]=='0))));

  // Out mirrors state
  assert property (out == state);

  // Counter step/rollover
  assert property ((cnt_reg < RATE) |-> ##1 (cnt_reg == $past(cnt_reg) + 24'd1));
  assert property ((cnt_reg >= RATE) |-> ##1 (cnt_reg == 24'd0));

  // Counter periodicity
  generate
    if (RATE > 0) begin
      assert property (tick |-> (!tick)[*RATE] ##1 tick);
      assert property ($past(tick) |-> (cnt_reg == 24'd1)); // first count after tick
    end else begin
      // RATE==0: tick every cycle, counter stays at 0
      assert property (tick ##1 tick);
      assert property ($past(tick) |-> (cnt_reg == 24'd0));
    end
  endgenerate

  // Debounce shift register updates only on tick, and with correct data
  genvar gk;
  generate
    for (gk=0; gk<WIDTH; gk++) begin: G_PER_BIT

      // Hold when no tick
      assert property ($past(!tick) |-> (debounce_reg[gk] == $past(debounce_reg[gk])));

      // Shift on tick (handle N==1 specially)
      if (N==1) begin
        assert property ($past(tick) |-> (debounce_reg[gk] == {$past(in[gk])}));
      end else begin
        assert property ($past(tick) |-> (debounce_reg[gk] == {$past(debounce_reg[gk][N-2:0]), $past(in[gk])}));
      end

      // State mapping from previous debounce_reg value
      assert property ($past(|debounce_reg[gk])==1'b0 |-> state[gk]==1'b0);
      assert property ($past(&debounce_reg[gk])==1'b1 |-> state[gk]==1'b1);
      assert property ($past(|debounce_reg[gk])==1'b1 && $past(&debounce_reg[gk])==1'b0 |-> state[gk]==$past(state[gk]));

      // Any state change must be caused by a tick in the previous cycle
      assert property ($changed(state[gk]) |-> $past(tick));

      // Functional debounce: N consecutive sampled 1s/0s drive state next cycle
      if (N==1) begin
        assert property ((tick && in[gk])  |-> ##1 (state[gk]==1'b1));
        assert property ((tick && !in[gk]) |-> ##1 (state[gk]==1'b0));
      end else begin
        // Sequence of N consecutive ticks with same input value
        sequence tick_pair1; (tick && in[gk]) ##(RATE+1) (tick && in[gk]); endsequence
        sequence tick_pair0; (tick && !in[gk]) ##(RATE+1) (tick && !in[gk]); endsequence
        assert property (tick_pair1[* (N-1)] |-> ##1 (state[gk]==1'b1));
        assert property (tick_pair0[* (N-1)] |-> ##1 (state[gk]==1'b0));
      end

      // Coverage: observe both directions and an ambiguous vector hold
      cover property ($rose(state[gk]));
      cover property ($fell(state[gk]));
      cover property ($past(|debounce_reg[gk]) && !$past(&debounce_reg[gk]) ##1 (state[gk]==$past(state[gk])));

    end
  endgenerate

  // Coverage: counter rollover event (RATE->0)
  cover property ($past(cnt_reg==RATE) && (cnt_reg==24'd0));

endmodule
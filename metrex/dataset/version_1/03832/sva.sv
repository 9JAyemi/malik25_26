// SystemVerilog Assertions for clk_gen
// Bind into DUT: bind clk_gen clk_gen_sva u_clk_gen_sva(.*);

module clk_gen_sva (
  input logic       clk, reset,
  input logic       clk1, clk2, clk4, fetch, alu_clk,
  input logic [7:0] state
);

  // Mirror DUT encodings
  localparam logic [7:0] S1=8'b00000001, S2=8'b00000010, S3=8'b00000100, S4=8'b00001000,
                         S5=8'b00010000, S6=8'b00100000, S7=8'b01000000, S8=8'b10000000,
                         idle=8'b00000000;

  // Basic combinational check
  assert property (@(posedge clk) clk1 == ~clk);
  assert property (@(negedge clk) clk1 == ~clk);

  // State legality (one-hot or idle)
  assert property (@(negedge clk) disable iff (reset) $onehot0(state));

  // State updates on negedge only; hold on posedge
  assert property (@(posedge clk) $stable({clk2,clk4,fetch,alu_clk,state}));

  // Reset behavior (post-NBA at same edge)
  assert property (@(negedge clk) reset |-> ##0 (clk2==1'b0 && clk4==1'b1 && fetch==1'b0 && alu_clk==1'b0 && state==idle));

  // Next-state sequence
  assert property (@(negedge clk) disable iff (reset) (state==S1)  |-> ##0 (state==S2));
  assert property (@(negedge clk) disable iff (reset) (state==S2)  |-> ##0 (state==S3));
  assert property (@(negedge clk) disable iff (reset) (state==S3)  |-> ##0 (state==S4));
  assert property (@(negedge clk) disable iff (reset) (state==S4)  |-> ##0 (state==S5));
  assert property (@(negedge clk) disable iff (reset) (state==S5)  |-> ##0 (state==S6));
  assert property (@(negedge clk) disable iff (reset) (state==S6)  |-> ##0 (state==S7));
  assert property (@(negedge clk) disable iff (reset) (state==S7)  |-> ##0 (state==S8));
  assert property (@(negedge clk) disable iff (reset) (state==S8)  |-> ##0 (state==S1));
  assert property (@(negedge clk) disable iff (reset) (state==idle)|-> ##0 (state==S1)); // after idle, go to S1

  // Output toggle rules (post-NBA at same edge)
  // clk2 toggles in all active states
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S1,S2,S3,S4,S5,S6,S7,S8}) |-> ##0 (clk2 != $past(clk2)));

  // clk4 toggles only in S2,S4,S6,S8; stable otherwise (incl. idle)
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S2,S4,S6,S8}) |-> ##0 (clk4 != $past(clk4)));
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S1,S3,S5,S7,idle}) |-> ##0 $stable(clk4));

  // fetch toggles only in S4,S8; stable otherwise (incl. idle)
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S4,S8}) |-> ##0 (fetch != $past(fetch)));
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S1,S2,S3,S5,S6,S7,idle}) |-> ##0 $stable(fetch));

  // alu_clk toggles only in S1,S2; stable otherwise (incl. idle)
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S1,S2}) |-> ##0 (alu_clk != $past(alu_clk)));
  assert property (@(negedge clk) disable iff (reset)
                   (state inside {S3,S4,S5,S6,S7,S8,idle}) |-> ##0 $stable(alu_clk));

  // Idle holds outputs (when not in reset)
  assert property (@(negedge clk) disable iff (reset) (state==idle) |-> ##0 $stable({clk2,clk4,fetch,alu_clk}));

  // Sanity: no X/Z after reset deasserted
  assert property (@(negedge clk) disable iff (reset) !$isunknown({clk2,clk4,fetch,alu_clk,clk1,state}));

  // Coverage
  cover property (@(negedge clk) disable iff (reset)
                  state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S4 ##
                  1 state==S5 ##1 state==S6 ##1 state==S7 ##1 state==S8 ##1 state==S1);
  cover property (@(negedge clk) disable iff (reset) (state==S4) ##0 (fetch != $past(fetch)));
  cover property (@(negedge clk) disable iff (reset) (state==S1) ##0 (alu_clk != $past(alu_clk)));

endmodule

// Bind into the DUT
bind clk_gen clk_gen_sva u_clk_gen_sva(.*);
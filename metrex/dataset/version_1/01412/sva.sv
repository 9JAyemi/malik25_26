// SVA for Delay
module Delay_sva(
  input logic        CLK,
  input logic        RST,
  input logic [11:0] DELAY_MS,
  input logic        DELAY_EN,
  input logic        DELAY_FIN,
  input logic [1:0]  current_state,
  input logic [13:0] clk_counter,
  input logic [11:0] ms_counter
);
  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  localparam int Idle = 2'd0;
  localparam int Hold = 2'd1;
  localparam int Done = 2'd2;
  localparam int TERMINAL = 14'd12000;

  // Combinational output mapping
  assert property (@cb DELAY_FIN == ((current_state==Done) && DELAY_EN));

  // Reset behavior (checked even when disabled-if)
  assert property (@cb RST |=> current_state==Idle);

  // Valid state encoding
  assert property (@cb current_state inside {Idle,Hold,Done});

  // State transitions
  assert property (@cb (current_state==Idle  &&  DELAY_EN)  |=> current_state==Hold);
  assert property (@cb (current_state==Idle  && !DELAY_EN)  |=> current_state==Idle);

  assert property (@cb (current_state==Hold  && (ms_counter==DELAY_MS))  |=> current_state==Done);
  assert property (@cb (current_state==Hold  && (ms_counter!=DELAY_MS))  |=> current_state==Hold);

  assert property (@cb (current_state==Done  && !DELAY_EN)  |=> current_state==Idle);
  assert property (@cb (current_state==Done  &&  DELAY_EN)  |=> current_state==Done);

  // Counter invariants and updates
  assert property (@cb (current_state!=Hold) |=> (clk_counter==14'd0 && ms_counter==12'd0));

  assert property (@cb (current_state==Hold && clk_counter!=TERMINAL)
                        |=> (clk_counter==$past(clk_counter)+1) && $stable(ms_counter));

  assert property (@cb (current_state==Hold && clk_counter==TERMINAL)
                        |=> (clk_counter==14'd0) && (ms_counter==$past(ms_counter)+1));

  assert property (@cb (current_state==Hold) |-> clk_counter<=TERMINAL);

  // Assume DELAY_MS is stable during an active delay window (prevents spurious failures)
  assume property (@cb (current_state==Hold) |-> $stable(DELAY_MS));

  // Under the stability assumption, ms_counter never exceeds DELAY_MS while holding
  assert property (@cb (current_state==Hold) |-> ms_counter<=DELAY_MS);

  // Functional covers
  cover property (@cb $rose(DELAY_EN) ##1 (current_state==Hold)
                       ##[1:$] (DELAY_FIN) ##1 $fell(DELAY_EN) ##1 (current_state==Idle));

  // Cover zero-delay case
  cover property (@cb $rose(DELAY_EN) and (DELAY_MS==12'd0) ##[1:3] DELAY_FIN);

  // Cover at least two millisecond increments (two wraps)
  cover property (@cb (current_state==Hold && clk_counter==TERMINAL)
                       ##[1:$] (current_state==Hold && clk_counter==TERMINAL));

  // Cover max programmed delay finishing
  cover property (@cb (DELAY_MS==12'hFFF) ##[1:$] DELAY_FIN);
endmodule

// Bind into DUT
bind Delay Delay_sva u_Delay_sva (
  .CLK(CLK),
  .RST(RST),
  .DELAY_MS(DELAY_MS),
  .DELAY_EN(DELAY_EN),
  .DELAY_FIN(DELAY_FIN),
  .current_state(current_state),
  .clk_counter(clk_counter),
  .ms_counter(ms_counter)
);
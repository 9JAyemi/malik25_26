// SVA checker for Delay
module Delay_sva #(
  parameter int unsigned TICK_MAX = 17'b11000011010100000
)(
  input  logic         CLK,
  input  logic         RST,
  input  logic  [11:0] DELAY_MS,
  input  logic         DELAY_EN,
  input  logic         DELAY_FIN,
  input  logic [31:0]  current_state,
  input  logic [16:0]  clk_counter,
  input  logic [11:0]  ms_counter
);
  // State encodings used by DUT
  localparam logic [31:0] S_IDLE = "Idle";
  localparam logic [31:0] S_HOLD = "Hold";
  localparam logic [31:0] S_DONE = "Done";

  default clocking cb @ (posedge CLK); endclocking
  default disable iff (RST);

  // Reset behavior (synchronous)
  assert property (@(posedge CLK) RST |=> current_state == S_IDLE)
    else $error("Reset must drive state to Idle");

  // State transition correctness
  assert property (current_state == S_IDLE &&  DELAY_EN |=> current_state == S_HOLD);
  assert property (current_state == S_IDLE && !DELAY_EN |=> current_state == S_IDLE);

  assert property (current_state == S_HOLD && (ms_counter == DELAY_MS) |=> current_state == S_DONE);
  assert property (current_state == S_HOLD && (ms_counter != DELAY_MS) |=> current_state == S_HOLD);

  assert property (current_state == S_DONE &&  DELAY_EN |=> current_state == S_DONE);
  assert property (current_state == S_DONE && !DELAY_EN |=> current_state == S_IDLE);

  // Default/illegal state recovery
  assert property (!(current_state inside {S_IDLE,S_HOLD,S_DONE}) |=> current_state == S_IDLE);

  // DELAY_FIN definition
  assert property (DELAY_FIN == (current_state == S_DONE && DELAY_EN));

  // Counters must be zero whenever not in HOLD (next cycle)
  assert property (current_state != S_HOLD |=> (clk_counter == '0 && ms_counter == '0));

  // clk_counter behavior in HOLD
  assert property (current_state == S_HOLD |-> clk_counter <= TICK_MAX);

  assert property (current_state == S_HOLD && (clk_counter != TICK_MAX)
                   |=> clk_counter == $past(clk_counter,1,RST) + 1
                    && ms_counter == $past(ms_counter,1,RST));

  assert property (current_state == S_HOLD && (clk_counter == TICK_MAX)
                   |=> clk_counter == '0
                    && ms_counter == $past(ms_counter,1,RST) + 1);

  // DONE implies counters will be cleared next cycle (since not HOLD)
  assert property (current_state == S_DONE |=> (clk_counter == '0 && ms_counter == '0));

  // Basic functional coverage
  cover property (current_state == S_IDLE && DELAY_EN ##1 current_state == S_HOLD);
  cover property (current_state == S_HOLD && (ms_counter == DELAY_MS) ##1 current_state == S_DONE);
  cover property (current_state == S_DONE && !DELAY_EN ##1 current_state == S_IDLE);

  // Cover: one ms tick (clk_counter wrap) while in HOLD
  cover property (current_state == S_HOLD && clk_counter == TICK_MAX ##1
                  clk_counter == '0 && ms_counter == $past(ms_counter,1,RST)+1);

  // Cover: full cycle Idle -> Hold -> Done -> Idle with EN protocol
  cover property (
    current_state == S_IDLE && DELAY_EN
    ##1 current_state == S_HOLD [*1:$]
    ##1 current_state == S_DONE && DELAY_EN
    ##1 current_state == S_DONE && !DELAY_EN
    ##1 current_state == S_IDLE
  );

  // Cover: zero-ms case completes immediately
  cover property (
    DELAY_MS == 12'h000 && current_state == S_IDLE && DELAY_EN
    ##1 current_state == S_HOLD
    ##1 current_state == S_DONE
  );

endmodule

// Bind into the DUT
bind Delay Delay_sva #(.TICK_MAX(17'b11000011010100000)) delay_sva_i (
  .CLK(CLK),
  .RST(RST),
  .DELAY_MS(DELAY_MS),
  .DELAY_EN(DELAY_EN),
  .DELAY_FIN(DELAY_FIN),
  .current_state(current_state),
  .clk_counter(clk_counter),
  .ms_counter(ms_counter)
);
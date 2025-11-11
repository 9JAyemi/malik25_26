// SVA for delay_module
module delay_module_sva (
  input  logic       CLK,
  input  logic       D,
  input  logic       SCD,
  input  logic       SCE,
  input  logic       RESET_B,
  input  logic       Q,
  input  logic [1:0] delay_counter
);

  // Synchronous reset behavior
  assert property (@(posedge CLK)
    !RESET_B |=> (Q==1'b0 && delay_counter==2'b00));

  // Knownness after reset deasserted
  assert property (@(posedge CLK) disable iff (!RESET_B)
    !$isunknown({Q,delay_counter}));

  // delay_counter stays within {0,1}
  assert property (@(posedge CLK) disable iff (!RESET_B)
    (delay_counter inside {2'b00,2'b01}));

  // Next-state of Q
  // If SCE==0 or not in delay state, Q captures D
  assert property (@(posedge CLK) disable iff (!RESET_B)
    ((!SCE) || (delay_counter==2'b00)) |=> (Q == $past(D)));

  // If in delay state with SCE==1, Q holds for one cycle
  assert property (@(posedge CLK) disable iff (!RESET_B)
    (SCE && (delay_counter!=2'b00)) |=> (Q == $past(Q)));

  // Next-state of delay_counter
  // SCE==0 always clears counter
  assert property (@(posedge CLK) disable iff (!RESET_B)
    (!SCE) |=> (delay_counter==2'b00));

  // With SCE==1 and not delayed, counter mirrors SCD (0->no delay, 1->enter delay)
  assert property (@(posedge CLK) disable iff (!RESET_B)
    (SCE && (delay_counter==2'b00)) |=> (delay_counter == $past(SCD)));

  // One-shot nature: any nonzero counter is cleared next cycle
  assert property (@(posedge CLK) disable iff (!RESET_B)
    (delay_counter!=2'b00) |=> (delay_counter==2'b00));

  // Delayed path timing: enter 1 for exactly one cycle when requested
  assert property (@(posedge CLK) disable iff (!RESET_B)
    (SCE && (delay_counter==2'b00) && SCD) |=> (delay_counter==2'b01) ##1 (delay_counter==2'b00));

  // Coverage
  cover property (@(posedge CLK) !RESET_B ##1 RESET_B); // reset then release
  cover property (@(posedge CLK) disable iff (!RESET_B)
    !SCE ##1 (Q==$past(D)) ); // direct load path
  cover property (@(posedge CLK) disable iff (!RESET_B)
    (SCE && delay_counter==2'b00 && !SCD) ##1 (Q==$past(D) && delay_counter==2'b00) ); // enabled no-delay
  cover property (@(posedge CLK) disable iff (!RESET_B)
    (SCE && delay_counter==2'b00 && SCD) ##1 (delay_counter==2'b01)
                                   ##1 (delay_counter==2'b00) ); // delayed sequence

endmodule

// Bind example (place in a testbench or package):
// bind delay_module delay_module_sva sva_i (.*,.delay_counter(delay_counter));
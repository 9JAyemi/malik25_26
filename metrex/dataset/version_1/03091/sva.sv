// SVA for sync_seq_circuit
module sync_seq_circuit_sva (
  input logic CLK_N,
  input logic RESET_B,
  input logic D,
  input logic Q
);

  // Asynchronous reset must clear Q immediately (NBA-aware)
  property p_async_reset_clears;
    @(negedge RESET_B) 1 |-> ##0 (Q == 1'b0);
  endproperty
  assert property (p_async_reset_clears);

  // While in reset, Q must be 0 at every clock
  assert property (@(posedge CLK_N) (!RESET_B) |-> (Q == 1'b0));

  // 0->1 transitions only occur when D==1 at that clock
  assert property (@(posedge CLK_N) disable iff (!RESET_B) $rose(Q) |-> D);

  // If D==1 at a clock, Q must be 1 by the next clock
  assert property (@(posedge CLK_N) disable iff (!RESET_B) D |=> Q);

  // If D==0 at a clock, Q must hold its previous value
  assert property (@(posedge CLK_N) disable iff (!RESET_B) !D |=> (Q == $past(Q,1,1'b0)));

  // No 1->0 drop without reset (monotonic while out of reset)
  assert property (@(posedge CLK_N) disable iff (!RESET_B) !($past(Q,1,1'b0) && !Q));

  // No unknown on Q while out of reset
  assert property (@(posedge CLK_N) disable iff (!RESET_B) !$isunknown(Q));

  // Coverage
  cover property (@(negedge RESET_B) 1);
  cover property (@(posedge RESET_B) 1);
  cover property (@(posedge CLK_N) disable iff (!RESET_B) (!Q && D) ##1 Q); // set event from 0
  cover property (@(posedge CLK_N) disable iff (!RESET_B) Q[*3]);           // hold high

endmodule

// Bind to DUT
bind sync_seq_circuit sync_seq_circuit_sva sva (.*);
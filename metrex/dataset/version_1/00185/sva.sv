// SVA for state_machine
// Quality-focused, concise checks + essential functional coverage

module state_machine_sva (
  input logic        clk,
  input logic        reset,
  input logic [8:0]  in_state,
  input logic        out1,
  input logic        out2
);

  default clocking cb @(posedge clk); endclocking

  // Sanity
  assert property ( !$isunknown({out1,out2}) ) else $error("X/Z on outputs");
  assert property ( !(out1 && out2) ) else $error("Both outputs high");

  // Asynchronous reset clears immediately and holds while asserted
  assert property (@(posedge reset) (!out1 && !out2))
    else $error("Async reset did not clear outputs");
  assert property ( reset |-> (!out1 && !out2) )
    else $error("Outputs not held low during reset");

  // Functional mapping at clock edge when not in reset
  assert property ( disable iff (reset) (in_state==9'd0) |-> (!out1 && !out2) )
    else $error("State 0 mapping failed");
  assert property ( disable iff (reset) (in_state==9'd1) |-> ( out1 && !out2) )
    else $error("State 1 mapping failed");
  assert property ( disable iff (reset) (in_state==9'd2) |-> (!out1 &&  out2) )
    else $error("State 2 mapping failed");
  assert property ( disable iff (reset) (in_state inside {[9'd3:9'd511]}) |-> (!out1 && !out2) )
    else $error("Default mapping failed");

  // Reverse implications (catch illegal 1s)
  assert property ( disable iff (reset) out1 |-> (in_state==9'd1) )
    else $error("out1 high outside state 1");
  assert property ( disable iff (reset) out2 |-> (in_state==9'd2) )
    else $error("out2 high outside state 2");

  // Coverage: hit each behavior and reset
  cover property ( $rose(reset) );
  cover property ( disable iff (reset) (in_state==9'd0) && !out1 && !out2 );
  cover property ( disable iff (reset) (in_state==9'd1) &&  out1 && !out2 );
  cover property ( disable iff (reset) (in_state==9'd2) && !out1 &&  out2 );
  cover property ( disable iff (reset) (in_state inside {[9'd3:9'd511]}) && !out1 && !out2 );

  // Post-reset functional covers
  cover property ( $fell(reset) ##1 (in_state==9'd1 && out1 && !out2) );
  cover property ( $fell(reset) ##1 (in_state==9'd2 && !out1 && out2) );

endmodule

// Bind into DUT
bind state_machine state_machine_sva sva_i (
  .clk     (clk),
  .reset   (reset),
  .in_state(in_state),
  .out1    (out1),
  .out2    (out2)
);
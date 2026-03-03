// SVA for up_down_counter
module up_down_counter_sva (
  input logic       CLK, UP, DOWN, LD,
  input logic [2:0] DIN,
  input logic [2:0] Q
);

  default clocking cb @(posedge CLK); endclocking
  // Ignore checks when any relevant signal is X/Z (esp. time 0, no reset present)
  default disable iff ($isunknown({UP,DOWN,LD,DIN,Q}));

  // Single concise next-state check capturing full priority and functionality
  property p_next_state;
    1 |=> Q == (LD        ? $past(DIN) :
                UP        ? $past(Q) + 3'd1 :
                DOWN      ? $past(Q) - 3'd1 :
                             $past(Q));
  endproperty
  assert property (p_next_state);

  // Explicit idle-hold (redundant with p_next_state but clarifies intent)
  assert property (!LD && !UP && !DOWN |=> $stable(Q));

  // Functional coverage
  cover property (LD                       ##1 Q == $past(DIN));
  cover property (!LD && UP                ##1 Q == $past(Q) + 3'd1);
  cover property (!LD && !UP && DOWN       ##1 Q == $past(Q) - 3'd1);
  cover property (!LD && !UP && !DOWN      ##1 Q == $past(Q));

  // Priority scenarios coverage
  cover property (LD && UP);                 // load wins over up
  cover property (LD && DOWN);               // load wins over down
  cover property (!LD && UP && DOWN ##1 Q == $past(Q) + 3'd1); // up wins over down

  // Wrap-around coverage (mod-8 behavior)
  cover property (!LD && UP        && $past(Q) == 3'd7 ##1 Q == 3'd0);
  cover property (!LD && !UP && DOWN && $past(Q) == 3'd0 ##1 Q == 3'd7);

endmodule

// Bind to DUT
bind up_down_counter up_down_counter_sva sva_inst (.*);
// SVA for counter: checks +1 mod-16 behavior, wrap, periodicity, no-X, and covers full cycle.
module counter_sva (input logic CLK, input logic [3:0] Q);

  default clocking cb @(posedge CLK); endclocking

  function bit known4 (logic [3:0] v); return !$isunknown(v); endfunction

  // No-X once past value is known
  property p_no_x;
    known4($past(Q)) |-> known4(Q);
  endproperty
  assert property (p_no_x);

  // Exact next-state: +1 with wrap at 15
  property p_inc_mod16;
    known4($past(Q)) |-> Q == (($past(Q)==4'hF) ? 4'h0 : $past(Q)+4'h1);
  endproperty
  assert property (p_inc_mod16);

  // Must change every cycle (no stutter)
  property p_change_every_cycle;
    known4($past(Q)) |-> Q != $past(Q);
  endproperty
  assert property (p_change_every_cycle);

  // Periodicity: repeats every 16 cycles
  property p_period16;
    known4($past(Q,16)) |-> Q == $past(Q,16);
  endproperty
  assert property (p_period16);

  // Coverage: see all states in order and wrap back to 0
  cover property (@cb
    Q==4'h0 ##1 Q==4'h1 ##1 Q==4'h2 ##1 Q==4'h3 ##1
    Q==4'h4 ##1 Q==4'h5 ##1 Q==4'h6 ##1 Q==4'h7 ##1
    Q==4'h8 ##1 Q==4'h9 ##1 Q==4'hA ##1 Q==4'hB ##1
    Q==4'hC ##1 Q==4'hD ##1 Q==4'hE ##1 Q==4'hF ##1 Q==4'h0
  );

  // Coverage: first time Q becomes known
  cover property (@cb known4(Q));

  // Coverage: explicit wrap event F -> 0
  cover property (@cb known4($past(Q)) && $past(Q)==4'hF && Q==4'h0);

endmodule

bind counter counter_sva u_counter_sva (.CLK(CLK), .Q(Q));
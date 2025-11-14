// SVA checker for my_register
module my_register_sva (
  input logic clk,
  input logic ena,
  input logic d,
  input logic clrn,
  input logic prn,
  input logic q
);

  default clocking cb @(posedge clk); endclocking

  // track first valid cycle for $past
  logic init_done;
  initial init_done = 1'b0;
  always @(posedge clk) init_done <= 1'b1;

  // Next-state function (matches DUT priority)
  function automatic logic next_q(logic q_i, logic ena_i, logic d_i, logic clrn_i, logic prn_i);
    if (clrn_i == 1'b0)       next_q = 1'b0;
    else if (prn_i == 1'b0)   next_q = 1'b1;
    else if (ena_i == 1'b1)   next_q = d_i;
    else                      next_q = q_i;
  endfunction

  // Core functional check: q equals function of previous-cycle inputs/state
  ap_functional: assert property ( disable iff (!init_done)
    q == next_q($past(q), $past(ena), $past(d), $past(clrn), $past(prn))
  );

  // No glitches: q changes only on clk rising edge
  ap_no_glitch: assert property ( disable iff (!init_done)
    $changed(q) |-> $rose(clk)
  );

  // Inputs known each clock; output known after update
  ap_inputs_known: assert property ( disable iff (!init_done)
    !$isunknown({clrn, prn, ena, d})
  );
  ap_q_known: assert property ( disable iff (!init_done)
    !$isunknown(q)
  );

  // Coverage: exercise all priority paths and hold
  cp_clear:   cover property ( disable iff (!init_done)
    ($past(clrn)==1'b0) && (q==1'b0)
  );
  cp_preset:  cover property ( disable iff (!init_done)
    ($past(clrn)!=1'b0 && $past(prn)==1'b0) && (q==1'b1)
  );
  cp_enable:  cover property ( disable iff (!init_done)
    ($past(clrn)!=1'b0 && $past(prn)!=1'b0 && $past(ena)==1'b1) && (q==$past(d))
  );
  cp_hold:    cover property ( disable iff (!init_done)
    ($past(clrn)!=1'b0 && $past(prn)!=1'b0 && $past(ena)==1'b0) && (q==$past(q))
  );
  // Both asserted low -> clear has priority
  cp_both_low: cover property ( disable iff (!init_done)
    ($past(clrn)==1'b0 && $past(prn)==1'b0) && (q==1'b0)
  );

endmodule

// Bind into the DUT
bind my_register my_register_sva u_my_register_sva (
  .clk (clk),
  .ena (ena),
  .d   (d),
  .clrn(clrn),
  .prn (prn),
  .q   (q)
);
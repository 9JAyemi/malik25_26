// SVA for counter: concise, high-quality checks and coverage
module counter_sva (
  input logic       CLK,
  input logic       CTRL,
  input logic       LOAD,
  input logic [3:0] D,
  input logic [3:0] Q
);

  default clocking cb @(posedge CLK); endclocking

  // Guard first-cycle $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Next-state functional equivalence (covers priority: CTRL > LOAD > INC)
  ap_next_state: assert property (
    Q == ( $past(CTRL) ? 4'd0
         : $past(LOAD) ? $past(D)
         : $past(Q) + 4'd1 )
  ) else $error("counter: next-state mismatch");

  // No X/Z on control inputs when sampled
  ap_no_x_ctrl_load: assert property ( !$isunknown({CTRL, LOAD}) )
    else $error("counter: CTRL/LOAD unknown");

  // No X/Z on D when used (LOAD and not overridden by CTRL)
  ap_no_x_D_when_used: assert property ( (LOAD && !CTRL) |-> !$isunknown(D) )
    else $error("counter: D unknown when LOAD");

  // No X/Z on Q post-update
  ap_no_x_Q: assert property ( !$isunknown(Q) )
    else $error("counter: Q unknown");

  // Key functional covers
  cv_ctrl:      cover property ( CTRL );                      // reset-to-zero path seen
  cv_load:      cover property ( !CTRL && LOAD );             // load path seen
  cv_inc:       cover property ( !CTRL && !LOAD );            // increment path seen
  cv_priority:  cover property ( CTRL && LOAD ##1 Q == 4'd0 );// CTRL dominates LOAD
  cv_wrap:      cover property ( !CTRL && !LOAD && Q==4'hF ##1 Q==4'h0 ); // wrap-around

  // Reachability of all Q values
  generate
    genvar i;
    for (i = 0; i < 16; i++) begin : gen_q_cov
      cover property ( Q == i[3:0] );
    end
  endgenerate

endmodule

// Bind into the DUT
bind counter counter_sva counter_sva_i (
  .CLK (CLK),
  .CTRL(CTRL),
  .LOAD(LOAD),
  .D   (D),
  .Q   (Q)
);
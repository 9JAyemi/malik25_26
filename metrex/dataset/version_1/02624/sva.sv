// SVA for d_ff_asr: synchronous set has priority over reset, else load D; no glitches.
module d_ff_asr_sva (
  input logic D,
  input logic S,
  input logic R,
  input logic CLK,
  input logic Q
);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness at each rising clock edge
  a_func: assert property (Q == (S ? 1'b1 : (R ? 1'b0 : D)))
    else $error("d_ff_asr: Q != mux(S,1,R,0,D) at posedge CLK");

  // Q may only change coincident with a rising CLK (no glitches)
  a_no_glitch: assert property (@(posedge CLK or posedge Q or negedge Q)
                                $changed(Q) |-> $rose(CLK))
    else $error("d_ff_asr: Q changed without a CLK rising edge");

  // Priority sanity (redundant with a_func but explicitly checks S dominates R)
  a_priority: assert property (S && R |-> Q == 1'b1)
    else $error("d_ff_asr: S should dominate R");

  // Coverage: exercise all control/data cases and output responses
  c_set:   cover property (S                 ##1 Q == 1'b1);
  c_rst:   cover property (!S && R           ##1 Q == 1'b0);
  c_ld1:   cover property (!S && !R && D     ##1 Q == 1'b1);
  c_ld0:   cover property (!S && !R && !D    ##1 Q == 1'b0);
  c_both:  cover property (S && R            ##1 Q == 1'b1);

  // Coverage: back-to-back data-driven toggles with no S/R
  c_tog_up_then_down: cover property (!S && !R && !D ##1 Q==1'b0 && !S && !R && D ##1 Q==1'b1 && !S && !R && !D ##1 Q==1'b0);
  c_tog_down_then_up: cover property (!S && !R && D  ##1 Q==1'b1 && !S && !R && !D ##1 Q==1'b0 && !S && !R && D  ##1 Q==1'b1);

endmodule

// Bind into DUT
bind d_ff_asr d_ff_asr_sva sva_inst (.D(D), .S(S), .R(R), .CLK(CLK), .Q(Q));
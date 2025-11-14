// Bindable SVA for mux_pipeline
module mux_pipeline_sva (
  input  logic        clk,
  input  logic [3:0]  IN,
  input  logic [1:0]  SEL,
  input  logic        EN,
  input  logic        out
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Functional correctness: 1-cycle pipelined mux behavior
  property p_pipeline_mux;
    past_valid |-> out === ($past(EN) ? $past(IN)[$past(SEL)] : 1'b0);
  endproperty
  assert property (p_pipeline_mux);

  // Knownness on capture: when capturing with EN=1, inputs must be known
  property p_inputs_known_on_capture;
    past_valid && $past(EN) |-> !$isunknown($past({SEL, IN}));
  endproperty
  assert property (p_inputs_known_on_capture);

  // Out should be known after first valid cycle
  property p_out_known_after_first;
    past_valid |-> !$isunknown(out);
  endproperty
  assert property (p_out_known_after_first);

  // No mid-cycle glitches (sampled at negedge as a concise proxy)
  assert property (@(negedge clk) $stable(out));

  // Coverage: observe each channel propagate both 0 and 1 with EN=1
  genvar i;
  generate
    for (i=0; i<4; i++) begin : cov_ch
      cover property (past_valid && $past(EN) && $past(SEL)==i && $past(IN[i])==1 && out==1);
      cover property (past_valid && $past(EN) && $past(SEL)==i && $past(IN[i])==0 && out==0);
    end
  endgenerate

  // Coverage: EN=0 forces 0
  cover property (past_valid && !$past(EN) && out==0);

endmodule

// Bind example:
// bind mux_pipeline mux_pipeline_sva sva (.*);
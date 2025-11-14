// SVA checkers and binds for the given design
// Focus: concise, high‑quality safety/functional checks + minimal but meaningful coverage

// ========== decade_counter assertions ==========
module decade_counter_sva (
  input clk,
  input pause,
  input resume,
  input reset,
  input [3:0] q
);
  // q must always be a valid BCD digit (0..9)
  property p_q_range;
    @(posedge clk) q <= 4'd9;
  endproperty
  assert property(p_q_range);

  // While reset is high at a clock edge, q must be 0
  property p_reset_forces_zero;
    @(posedge clk) reset |-> (q == 4'd0);
  endproperty
  assert property(p_reset_forces_zero);

  // When disabled (pause && !resume), hold value
  property p_hold_on_pause_only;
    @(posedge clk) disable iff (reset)
      (pause && !resume) |=> $stable(q);
  endproperty
  assert property(p_hold_on_pause_only);

  // When enabled (!pause || resume), increment modulo 10
  // Covers both normal enable and "resume overrides pause"
  property p_increment_when_enabled;
    @(posedge clk) disable iff (reset)
      (!pause || resume) |-> ( $past(q) == 4'd9 ? (q == 4'd0) : (q == $past(q) + 4'd1) );
  endproperty
  assert property(p_increment_when_enabled);

  // Coverage: see a wrap 9->0 when enabled
  cover property (@(posedge clk) disable iff (reset)
    (!pause || resume) && ($past(q)==4'd9) ##1 (q==4'd0));

  // Coverage: see a hold under pause without resume
  cover property (@(posedge clk) disable iff (reset)
    (pause && !resume) && $stable(q));

  // Coverage: explicit "resume overrides pause" increment
  cover property (@(posedge clk) disable iff (reset)
    (pause && resume) |-> (q == ($past(q)==4'd9 ? 4'd0 : $past(q)+1)));
endmodule

bind decade_counter decade_counter_sva dc_sva (.*);

// ========== edge_detection assertions ==========
module edge_detection_sva (
  input clk,
  input [7:0] in,
  input [7:0] anyedge
);
  // Guard first-cycle $past
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Accumulate exact bitmask of rising edges: anyedge <- anyedge + (in & ~past(in))
  property p_accumulate_rise_mask;
    @(posedge clk) past_valid |-> ( anyedge == $past(anyedge) + (in & ~ $past(in)) );
  endproperty
  assert property(p_accumulate_rise_mask);

  // Coverage: single-bit rise
  cover property (@(posedge clk) past_valid && ($countones(in & ~ $past(in)) == 1));

  // Coverage: multi-bit simultaneous rises
  cover property (@(posedge clk) past_valid && ($countones(in & ~ $past(in)) >= 2));

  // Coverage: overflow wrap (mod-256)
  cover property (@(posedge clk) past_valid && (anyedge < $past(anyedge)));
endmodule

bind edge_detection edge_detection_sva ed_sva (.*);

// ========== top_module assertions (incl. functional_module result) ==========
module top_module_sva (
  input clk,
  // hierarchical access to internal wires via bind context
  input [3:0] counter_output,
  input [7:0] edge_output,
  input [7:0] final_output
);
  // final_output must be the pure combinational sum (zero-extend counter)
  property p_final_is_sum;
    @(posedge clk) final_output == (edge_output + {4'h0, counter_output});
  endproperty
  assert property(p_final_is_sum);

  // Coverage: observe that counter increment alone increments final_output by 1
  // (i.e., edge_output stable and counter enabled/advances)
  property p_cover_final_increments_with_counter_only;
    @(posedge clk)
      $stable(edge_output) && ($past(counter_output) != counter_output) |->
      (final_output == $past(edge_output) + {4'h0, counter_output});
  endproperty
  cover property(p_cover_final_increments_with_counter_only);
endmodule

bind top_module top_module_sva top_sva (
  .clk(clk),
  .counter_output(counter_output),
  .edge_output(edge_output),
  .final_output(final_output)
);
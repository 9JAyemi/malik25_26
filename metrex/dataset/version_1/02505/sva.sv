// SVA for top_module
// Bind-friendly checker module plus bind statement.
// Focused, high-quality properties with key covers.

module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic  [7:0]  data_in,
  input logic         valid_in,
  input logic         ready_out,
  input logic  [3:0]  seq_length_out,
  input logic  [3:0]  seq_length_current,
  input logic  [3:0]  seq_length_max,
  input logic  [3:0]  seq_length_out_reg
);

  default clocking cb @(posedge clk); endclocking

  // $past guard and visibility control for seq_length_out (no reset on reg)
  logic past_valid, seen_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;
  always_ff @(posedge clk) begin
    if (reset) seen_valid <= 1'b0;
    else if (valid_in) seen_valid <= 1'b1;
  end

  // Reset behavior
  assert property (reset |-> (seq_length_current==4'd0 && seq_length_max==4'd0 && ready_out==1'b0));

  // Handshake: ready_out mirrors valid_in when not in reset
  assert property (!reset |-> ready_out==valid_in);

  // seq_length_current update rules
  assert property (!reset && past_valid && valid_in &&  data_in[0] |-> seq_length_current == (($past(seq_length_current)+1) & 4'hF));
  assert property (!reset && past_valid && valid_in && !data_in[0] |-> seq_length_current == 4'd0);
  assert property (!reset && past_valid && !valid_in            |-> seq_length_current == $past(seq_length_current));

  // seq_length_max update rules (pre-state compare; monotonic)
  assert property (!reset && past_valid &&  valid_in && ($past(seq_length_current) > $past(seq_length_max))
                   |-> seq_length_max == $past(seq_length_current));
  assert property (!reset && past_valid && !(valid_in && ($past(seq_length_current) > $past(seq_length_max)))
                   |-> seq_length_max == $past(seq_length_max));
  assert property (!reset && past_valid |-> seq_length_max >= $past(seq_length_max));

  // Connectivity: assign seq_length_out = seq_length_out_reg;
  assert property (seq_length_out == seq_length_out_reg);

  // seq_length_out behavior (separate always_ff, 1-cycle behind max; hold when !valid)
  assert property (!reset && past_valid && valid_in
                   |-> seq_length_out == $past(seq_length_max));
  assert property (!reset && past_valid && seen_valid && !valid_in
                   |-> seq_length_out == $past(seq_length_out));

  // Key coverage
  cover property (reset);
  cover property (!reset && valid_in && data_in[0] [*3]); // 3 consecutive increments
  cover property (!reset && valid_in && ($past(seq_length_current) > $past(seq_length_max))); // max update event
  cover property (!reset && past_valid && ($past(seq_length_current)==4'hF) && valid_in && data_in[0]
                  && seq_length_current==4'h0); // wrap-around on increment
  cover property (!reset && !valid_in ##1 valid_in && ready_out); // handshake toggle

endmodule

bind top_module top_module_sva
(
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .valid_in(valid_in),
  .ready_out(ready_out),
  .seq_length_out(seq_length_out),
  .seq_length_current(seq_length_current),
  .seq_length_max(seq_length_max),
  .seq_length_out_reg(seq_length_out_reg)
);
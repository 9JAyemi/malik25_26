// SVA for dffr: concise, high-quality checks and coverage
module dffr_sva #(parameter SIZE=1)
(
  input              clk,
  input              rst,
  input              se,
  input  [SIZE-1:0]  din,
  input  [SIZE-1:0]  si,
  input  [SIZE-1:0]  q,
  input  [SIZE-1:0]  so
);

  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Priority and next-state check
  property p_next_state;
    @(posedge clk) disable iff (!past_valid)
      q == ($past(se) ? $past(si) : ($past(rst) ? '0 : $past(din)));
  endproperty
  assert property (p_next_state);

  // so mirrors q
  assert property (@(posedge clk) so == q);

  // No glitches between clocks
  assert property (@(posedge clk) disable iff (!past_valid) $stable(q));
  assert property (@(posedge clk) disable iff (!past_valid) $stable(so));

  // X checks on controls and selected data
  assert property (@(posedge clk) !$isunknown({se, rst}));
  assert property (@(posedge clk) disable iff (!past_valid) ($past(se) |-> !$isunknown($past(si))));
  assert property (@(posedge clk) disable iff (!past_valid) (!$past(se) && !$past(rst) |-> !$isunknown($past(din))));

  // Targeted coverage: all functional paths + SE toggles
  cover property (@(posedge clk) disable iff (!past_valid) ($past(se) && (q == $past(si))));
  cover property (@(posedge clk) disable iff (!past_valid) (!$past(se) && $past(rst) && (q == '0)));
  cover property (@(posedge clk) disable iff (!past_valid) (!$past(se) && !$past(rst) && (q == $past(din))));
  cover property (@(posedge clk) $rose(se));
  cover property (@(posedge clk) $fell(se));

endmodule

bind dffr dffr_sva #(.SIZE(SIZE)) dffr_sva_i (
  .clk(clk), .rst(rst), .se(se), .din(din), .si(si), .q(q), .so(so)
);
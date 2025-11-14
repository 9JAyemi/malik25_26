// SVA for CDC_synchronizer
// Bind into DUT to access internals (ff1_out, ff2_out, enable, i)

module CDC_synchronizer_sva #(parameter int n=8, t=2) ();

  // Default clock
  default clocking cb @(posedge clk_in); endclocking

  // Track availability of $past()
  bit past_valid;
  always @(posedge clk_in) past_valid <= 1'b1;

  // Parameter sanity
  initial begin
    assert (n > 0) else $error("CDC_synchronizer: n must be > 0");
    assert (t >= 0) else $error("CDC_synchronizer: t must be >= 0");
  end

  // Combinational enable at posedge simplifies to ~rst_in
  assert property (enable == ~rst_in);

  // Stage-1 sampler: ff1_out captures data_in every cycle
  assert property (past_valid |-> ff1_out == $past(data_in));

  // Counter behavior and stage-2 sampler cadence
  assert property (past_valid && ($past(i) < t) |-> i == $past(i) + 1);
  assert property (past_valid && !($past(i) < t) |-> i == 0);
  assert property (past_valid && ($past(i) < t) |-> ff2_out == $past(ff2_out));          // hold between updates
  assert property (past_valid && !($past(i) < t) |-> ff2_out == $past(ff1_out));         // update on rollover
  assert property (past_valid && $changed(ff2_out) |-> !($past(i) < t));                 // only change on rollover

  // Output gating: updates only when rst_in==0, holds when rst_in==1
  assert property (rst_in |-> data_out == $past(data_out));
  assert property (!rst_in |-> data_out == $past(ff2_out));
  assert property ($changed(data_out) |-> !rst_in);

  // Basic X-prop safety on key outputs after first cycle (optional but useful)
  assert property (past_valid |-> !$isunknown({ff1_out, ff2_out, data_out})));

  // Coverage
  cover property (past_valid && !($past(i) < t) ##1 ($rose($changed(ff2_out)) || $changed(ff2_out)));
  cover property (!rst_in ##1 $changed(data_out));
  cover property (past_valid && ($past(i) == t-1) ##1 (i == t)); // counter approaching rollover
  cover property (!rst_in throughout [*3] ##1 $changed(data_in) ##[1:$] $changed(data_out));

endmodule

bind CDC_synchronizer CDC_synchronizer_sva #(.n(n), .t(t)) cdc_sva_inst();
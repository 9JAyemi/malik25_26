// SVA for mig_7series_v2_3_poc_edge_store
// Concise, high-quality checks and coverage

module mig_7series_v2_3_poc_edge_store_sva #(
  parameter int TAPCNTRWIDTH = 7,
  parameter int TAPSPERKCLK  = 112
)(
  input logic                           clk,
  input logic                           run_polarity,
  input logic                           run_end,
  input logic                           select0,
  input logic                           select1,
  input logic [TAPCNTRWIDTH-1:0]        tap,
  input logic [TAPCNTRWIDTH-1:0]        run,
  input logic [TAPCNTRWIDTH-1:0]        fall_lead,
  input logic [TAPCNTRWIDTH-1:0]        fall_trail,
  input logic [TAPCNTRWIDTH-1:0]        rise_lead,
  input logic [TAPCNTRWIDTH-1:0]        rise_trail
);

  // local deriveds (mirror DUT behavior)
  logic run_end_this;
  logic [TAPCNTRWIDTH-1:0] te_calc;

  assign run_end_this = run_end & select0 & select1;
  assign te_calc = (run > tap)
                 ? (tap + TAPSPERKCLK[TAPCNTRWIDTH-1:0] - run)
                 : (tap - run);

  // past-valid guard (no explicit reset in DUT)
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Updates on run_end_this with polarity = 1
  assert property (disable iff (!past_valid)
    $past(run_end_this & run_polarity)
    |-> ( fall_lead == $past(tap)
       && rise_trail == $past(te_calc)
       && rise_lead == $past(rise_lead)
       && fall_trail == $past(fall_trail))
  );

  // Updates on run_end_this with polarity = 0
  assert property (disable iff (!past_valid)
    $past(run_end_this & ~run_polarity)
    |-> ( rise_lead == $past(tap)
       && fall_trail == $past(te_calc)
       && fall_lead == $past(fall_lead)
       && rise_trail == $past(rise_trail))
  );

  // Hold when no qualified run_end
  assert property (disable iff (!past_valid)
    !$past(run_end_this)
    |-> ( fall_lead == $past(fall_lead)
       && fall_trail == $past(fall_trail)
       && rise_lead == $past(rise_lead)
       && rise_trail == $past(rise_trail))
  );

  // No update when run_end asserted but not both selects
  assert property (disable iff (!past_valid)
    $past(run_end & ~(select0 & select1))
    |-> ( fall_lead == $past(fall_lead)
       && fall_trail == $past(fall_trail)
       && rise_lead == $past(rise_lead)
       && rise_trail == $past(rise_trail))
  );

  // Coverage: both polarities update
  cover property (
    run_end_this & run_polarity ##1
      (fall_lead == $past(tap) && rise_trail == $past(te_calc))
  );

  cover property (
    run_end_this & ~run_polarity ##1
      (rise_lead == $past(tap) && fall_trail == $past(te_calc))
  );

  // Coverage: both trailing_edge branches exercised at update time
  cover property (
    run_end_this & run_polarity & (run > tap) ##1 rise_trail == $past(te_calc)
  );

  cover property (
    run_end_this & ~run_polarity & (run <= tap) ##1 fall_trail == $past(te_calc)
  );

  // Coverage: gate-off due to selects low
  cover property (
    run_end & ~(select0 & select1) ##1
      (fall_lead == $past(fall_lead)
    && fall_trail == $past(fall_trail)
    && rise_lead == $past(rise_lead)
    && rise_trail == $past(rise_trail))
  );

endmodule

// Example bind (tool-dependent parameter capture from bound scope)
bind mig_7series_v2_3_poc_edge_store
  mig_7series_v2_3_poc_edge_store_sva #(
    .TAPCNTRWIDTH(TAPCNTRWIDTH),
    .TAPSPERKCLK (TAPSPERKCLK)
  ) poc_edge_store_sva_i (
    .clk, .run_polarity, .run_end, .select0, .select1, .tap, .run,
    .fall_lead, .fall_trail, .rise_lead, .rise_trail
  );
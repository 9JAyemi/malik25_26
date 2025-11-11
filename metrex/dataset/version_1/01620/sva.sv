// SVA checker for mig_7series_v4_0_poc_tap_base
// Bind this checker to the DUT instance.
// Example:
// bind mig_7series_v4_0_poc_tap_base poc_tap_base_sva #(
//   .SAMPCNTRWIDTH(SAMPCNTRWIDTH),
//   .TAPCNTRWIDTH(TAPCNTRWIDTH),
//   .TAPSPERKCLK(TAPSPERKCLK)
// ) u_poc_tap_base_sva (.*);

module poc_tap_base_sva #(
  parameter int SAMPCNTRWIDTH = 8,
  parameter int TAPCNTRWIDTH  = 7,
  parameter int TAPSPERKCLK   = 112
)(
  input  logic                          clk,
  input  logic                          rst,
  // DUT I/Os used by assertions
  input  logic                          psdone,
  input  logic                          poc_sample_pd,
  input  logic                          psincdec,
  input  logic                          psen,
  input  logic [TAPCNTRWIDTH-1:0]       run,
  input  logic                          run_end,
  input  logic                          run_too_small,
  input  logic                          run_polarity,
  input  logic [SAMPCNTRWIDTH-1:0]      samp_cntr,
  input  logic [SAMPCNTRWIDTH:0]        samps_hi,
  input  logic [SAMPCNTRWIDTH:0]        samps_hi_held,
  input  logic [TAPCNTRWIDTH-1:0]       tap,
  input  logic [1:0]                    sm,
  input  logic                          samps_zero,
  input  logic                          samps_one,
  input  logic [SAMPCNTRWIDTH:0]        samples,
  input  logic [SAMPCNTRWIDTH:0]        samps_solid_thresh
);

  localparam int TAP_MAX      = TAPSPERKCLK;
  localparam int TAP_LAST     = TAPSPERKCLK-1;
  localparam int RUN_SMALL_TH = TAPSPERKCLK/4;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  assert property (psincdec) else $error("psincdec must be 1'b1 at all times");
  assert property (!$isunknown({sm, psen, psdone, run_end, run_too_small, run_polarity, tap}));

  // Reset behavior (checked during reset)
  assert property (rst |-> (psen==0 && sm==2'd0 && run_polarity==0 &&
                            run==0 && run_end==0 &&
                            samp_cntr==0 && samps_hi==0 && samps_hi_held==0 &&
                            tap==0));

  // State encoding and transitions
  assert property (sm inside {2'd0,2'd1,2'd2,2'd3});
  assert property (sm==2'd0 |=> (sm==2'd0 || sm==2'd1));
  assert property (sm==2'd1 |=> sm==2'd2);
  assert property (sm==2'd2 |=> sm==2'd3);
  assert property (sm==2'd3 && !psdone |=> sm==2'd3);
  assert property (sm==2'd3 &&  psdone |=> sm==2'd0);

  // psen is asserted iff in SM=2 (one-cycle)
  assert property (psen == (sm==2'd2));

  // tap update: increment with wrap only when leaving SM=2
  assert property (sm==2'd2 |=> tap == (($past(tap)==TAP_LAST) ? '0 : $past(tap)+1));
  assert property (sm!=2'd2 |=> tap==$past(tap));

  // samp_cntr and samps_hi behavior
  assert property (sm==2'd2 |=> samp_cntr==0);
  assert property (sm inside {2'd1,2'd3} |=> samp_cntr==$past(samp_cntr));
  assert property (sm==2'd2 |=> samps_hi==0);
  assert property (sm inside {2'd1,2'd3} |=> samps_hi==$past(samps_hi));

  // Capture of samps_hi_held on SM=2, otherwise stable
  assert property (sm==2'd2 |=> samps_hi_held == $past(samps_hi));
  assert property (sm!=2'd2 |=> samps_hi_held == $past(samps_hi_held));

  // samps_one/samps_zero are 1-cycle delayed compares
  assert property (samps_one == ($past(samps_hi) >= $past(samps_solid_thresh)));
  assert property (samps_zero == (($past(samples) + {{SAMPCNTRWIDTH{1'b0}},1'b1}) - $past(samps_hi) >= $past(samps_solid_thresh)));

  // run counter updates only in SM=2
  assert property (sm inside {2'd0,2'd1,2'd3} |=> run==$past(run));

  // run_end behavior and run update semantics in SM=2
  // If run_end asserted, next run must be 0 and polarity must toggle
  assert property (sm==2'd2 && run_end |-> (run==0) && (run_polarity != $past(run_polarity)));
  // If no run_end, next run increments and polarity holds
  assert property (sm==2'd2 && !run_end |-> (run == $past(run)+1) && (run_polarity == $past(run_polarity)));
  // run_end only in SM=2
  assert property (run_end |-> sm==2'd2);

  // Polarity update rules in SM=2 based on solid regions
  assert property (sm==2'd2 &&  $past(run_polarity)==1 && samps_zero |-> run_polarity==0);
  assert property (sm==2'd2 &&  $past(run_polarity)==0 && samps_one  |-> run_polarity==1);
  assert property (sm==2'd2 && !(($past(run_polarity)==1 && samps_zero) ||
                                 ($past(run_polarity)==0 && samps_one)) |-> run_polarity==$past(run_polarity));

  // run_too_small is a 1-cycle delayed function of run_end and run
  assert property (run_too_small == ($past(run_end) && ($past(run) < RUN_SMALL_TH)));

  // Coverage
  cover property (sm==2'd0 ##1 sm==2'd1 ##1 sm==2'd2 && psen ##1 sm==2'd3 && psdone ##1 sm==2'd0);
  cover property (sm==2'd2 && $past(tap)==TAP_LAST ##1 tap==0);
  cover property (sm==2'd2 && samps_one && $past(run_polarity)==0 && run_end);
  cover property (sm==2'd2 && samps_zero && $past(run_polarity)==1 && run_end);
  cover property ($past(run_end) && ($past(run) < RUN_SMALL_TH) && run_too_small);

endmodule
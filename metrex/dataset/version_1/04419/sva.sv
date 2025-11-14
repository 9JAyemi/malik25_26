// SVA for PIO_TO_CTRL
// Focused, concise checks + coverage

`ifndef SYNTHESIS
module PIO_TO_CTRL_sva (
  input  logic clk,
  input  logic rst_n,
  input  logic req_compl,
  input  logic compl_done,
  input  logic cfg_to_turnoff,
  input  logic trn_pending,       // internal reg from DUT
  input  logic cfg_turnoff_ok     // output reg from DUT
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Reset value check (one-cycle after reset observed)
  assert property (@(posedge clk) !rst_n |=> (!trn_pending && !cfg_turnoff_ok));

  // Next-state functional equivalence
  assert property (trn_pending == ($past(trn_pending) && !$past(compl_done)) ||
                                   (!$past(trn_pending) &&  $past(req_compl)));
  assert property (cfg_turnoff_ok == $past(cfg_to_turnoff && !trn_pending));

  // Edge-cause checks
  assert property ($rose(trn_pending) |-> $past(!trn_pending && req_compl));
  assert property ($fell(trn_pending) |-> $past(trn_pending && compl_done));
  assert property ($rose(cfg_turnoff_ok) |-> $past(cfg_to_turnoff && !trn_pending));
  assert property ($fell(cfg_turnoff_ok) |-> !$past(cfg_to_turnoff && !trn_pending));

  // Known-value checks out of reset
  assert property (!$isunknown(trn_pending));
  assert property (!$isunknown(cfg_turnoff_ok));

  // Key coverage
  cover property (!trn_pending && req_compl ##1 trn_pending);                    // set pending
  cover property (trn_pending && compl_done ##1 !trn_pending);                   // clear pending
  cover property (!trn_pending && req_compl && compl_done ##1 trn_pending);      // both high when idle -> set
  cover property (trn_pending && req_compl && compl_done ##1 !trn_pending);      // both high when busy -> clear
  cover property (cfg_to_turnoff && !trn_pending ##1 cfg_turnoff_ok);            // turnoff OK asserted
  cover property ((trn_pending or !cfg_to_turnoff) ##1 !cfg_turnoff_ok);         // turnoff OK deasserted
endmodule

bind PIO_TO_CTRL PIO_TO_CTRL_sva sva_i (.*);
`endif
// SVA for SRFF_sp: concise but complete checks and coverage
`ifndef SYNTHESIS
module SRFF_sp_sva
(
  input logic clock,
  input logic reset,
  input logic io_input_set,
  input logic io_input_reset,
  input logic io_input_asyn_reset,
  input logic io_output_data,
  input logic _T_14 // internal state
);

  // Establish a safe $past window
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  default clocking cb @(posedge clock); endclocking

  // Combinational output mapping (asynchronous gating dominates)
  assert property (@cb io_output_data == (io_input_asyn_reset ? 1'b0 : _T_14))
    else $error("io_output_data mapping broken");

  // Async reset must force output low immediately and hold while asserted
  assert property (@(posedge io_input_asyn_reset) io_output_data == 1'b0)
    else $error("io_output_data must go low on async reset edge");
  assert property (@cb io_input_asyn_reset |-> (io_output_data == 1'b0 throughout io_input_asyn_reset))
    else $error("io_output_data must stay low while async reset=1");

  // Synchronous reset clears state
  assert property (@cb reset |-> (_T_14 == 1'b0))
    else $error("state must clear on sync reset");

  // Next-state function (one-cycle lookback), with priority: async_reset > set > reset > hold
  assert property (@cb disable iff (!past_valid || reset)
                   _T_14 == ( $past(io_input_asyn_reset) ? 1'b0 :
                              $past(io_input_set)         ? 1'b1 :
                              $past(io_input_reset)       ? 1'b0 :
                                                            $past(_T_14)))
    else $error("next-state mismatch");

  // Explicit priority check: set dominates reset when both high (and no async reset)
  assert property (@cb disable iff (reset)
                   io_input_set && io_input_reset && !io_input_asyn_reset |=> _T_14 == 1'b1)
    else $error("set must dominate reset when both asserted");

  // Known-value checks on state and output
  assert property (@cb !$isunknown({_T_14, io_output_data}))
    else $error("X/Z detected on state/output");

  // --------------------------------------
  // Functional coverage
  // --------------------------------------

  // Cover set operation driving 1
  cover property (@cb disable iff (reset)
                  !$past(io_input_asyn_reset) && $past(io_input_set) && !$past(io_input_reset) ##0
                  (_T_14 == 1'b1) && (io_output_data == 1'b1));

  // Cover reset operation driving 0
  cover property (@cb disable iff (reset)
                  !$past(io_input_asyn_reset) && !$past(io_input_set) && $past(io_input_reset) ##0
                  (_T_14 == 1'b0) && (io_output_data == 1'b0));

  // Cover both set and reset asserted simultaneously (set wins)
  cover property (@cb disable iff (reset)
                  $past(io_input_set && io_input_reset && !io_input_asyn_reset) ##0
                  (_T_14 == 1'b1));

  // Cover async reset edge: immediate output low and state cleared next cycle
  cover property (@cb disable iff (reset)
                  $rose(io_input_asyn_reset) ##0 (io_output_data == 1'b0) ##1 (_T_14 == 1'b0));

  // Cover 0->1->0 sequence through set then reset (no async reset)
  cover property (@cb disable iff (reset)
                  !io_input_asyn_reset && (_T_14 == 1'b0) ##1
                  (io_input_set && !io_input_reset) ##1
                  (_T_14 == 1'b1) ##1
                  (io_input_reset && !io_input_set) ##1
                  (_T_14 == 1'b0));

endmodule

// Bind SVA to DUT (expose internal _T_14)
bind SRFF_sp SRFF_sp_sva
(
  .clock(clock),
  .reset(reset),
  .io_input_set(io_input_set),
  .io_input_reset(io_input_reset),
  .io_input_asyn_reset(io_input_asyn_reset),
  .io_output_data(io_output_data),
  ._T_14(_T_14)
);
`endif
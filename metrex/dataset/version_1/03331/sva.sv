// SVA for flow_control_processing
// Bind this file to the DUT; focuses on functional equivalence, state update, reset, and X-prop

module flow_control_processing_sva #(
  parameter int SYMBOLS_PER_BEAT = 4,
  parameter int BITS_PER_SYMBOL  = 8
)(
  input  logic                                  clock,
  input  logic                                  reset,

  input  logic                                  internal_output_is_valid,
  input  logic                                  ena,
  input  logic                                  ready_out,

  input  logic                                  stall,
  input  logic                                  valid_out,

  input  logic [SYMBOLS_PER_BEAT*BITS_PER_SYMBOL-1:0] data_out,
  input  logic                                  eop_out,
  input  logic                                  sop_out,

  // internal state
  input  logic [SYMBOLS_PER_BEAT*BITS_PER_SYMBOL-1:0] data_out_d1,
  input  logic                                  sop_out_d1,
  input  logic                                  eop_out_d1
);

  localparam int DW = SYMBOLS_PER_BEAT*BITS_PER_SYMBOL;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Combinational definitions
  assert property (stall == !ready_out)
    else $error("stall must equal !ready_out");

  assert property (valid_out == (internal_output_is_valid && ena))
    else $error("valid_out must equal internal_output_is_valid && ena");

  // Output muxing correctness
  assert property (!valid_out |-> (data_out == '0 && sop_out == 1'b0 && eop_out == 1'b0))
    else $error("Outputs must be 0 when not valid");

  assert property (valid_out |-> (data_out == data_out_d1 && sop_out == sop_out_d1 && eop_out == eop_out_d1))
    else $error("Outputs must reflect the registered state when valid");

  // State update semantics (next-state relation)
  assert property (data_out_d1 == ($past(valid_out) ? $past(data_out_d1) : '0))
    else $error("data_out_d1 next-state mismatch");

  assert property (sop_out_d1  == ($past(valid_out) ? $past(sop_out_d1)  : 1'b0))
    else $error("sop_out_d1 next-state mismatch");

  assert property (eop_out_d1  == ($past(valid_out) ? $past(eop_out_d1)  : 1'b0))
    else $error("eop_out_d1 next-state mismatch");

  // Stability while valid is held
  assert property (valid_out && $past(valid_out) |-> $stable({data_out_d1, sop_out_d1, eop_out_d1}))
    else $error("Registered state must hold while valid_out is asserted");

  // Upon deasserting valid, state clears in one cycle
  assert property ($past(valid_out) && !valid_out |-> (data_out_d1 == '0 && sop_out_d1 == 1'b0 && eop_out_d1 == 1'b0))
    else $error("State must clear when valid_out deasserts");

  // Reset effects (use separate assertions without disable iff)
  property p_reset_clears_regs;
    @(posedge clock) $past(reset) |-> (data_out_d1 == '0 && sop_out_d1 == 1'b0 && eop_out_d1 == 1'b0);
  endproperty
  assert property (p_reset_clears_regs)
    else $error("Registers not cleared after reset");

  property p_outputs_zero_during_reset;
    @(posedge clock) reset |-> (data_out == '0 && sop_out == 1'b0 && eop_out == 1'b0);
  endproperty
  assert property (p_outputs_zero_during_reset)
    else $error("Outputs must be 0 during reset");

  // X-prop checks on DUT outputs
  assert property (!$isunknown({stall, valid_out, sop_out, eop_out}))
    else $error("Unknown on 1-bit outputs");

  assert property (!$isunknown(data_out))
    else $error("Unknown on data_out");

  // Basic coverage
  cover property (!valid_out ##1 valid_out ##1 !valid_out);         // valid toggle
  cover property (ready_out ##1 !ready_out ##1 ready_out);          // stall toggle via ready_out
  cover property (reset ##1 !reset ##1 !valid_out);                  // reset exit
  cover property (valid_out [*3]);                                   // sustained valid

endmodule

// Bind into DUT
bind flow_control_processing flow_control_processing_sva #(
  .SYMBOLS_PER_BEAT(SYMBOLS_PER_BEAT),
  .BITS_PER_SYMBOL(BITS_PER_SYMBOL)
) i_flow_control_processing_sva (
  .clock(clock),
  .reset(reset),
  .internal_output_is_valid(internal_output_is_valid),
  .ena(ena),
  .ready_out(ready_out),
  .stall(stall),
  .valid_out(valid_out),
  .data_out(data_out),
  .eop_out(eop_out),
  .sop_out(sop_out),
  .data_out_d1(data_out_d1),
  .sop_out_d1(sop_out_d1),
  .eop_out_d1(eop_out_d1)
);
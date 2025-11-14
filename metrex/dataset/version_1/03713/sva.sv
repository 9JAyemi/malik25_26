// SVA checker for comparator
// Bind this checker to the DUT: bind comparator comparator_chk comp_sva (.*);

module comparator_chk (
  input  logic [3:0] in0,
  input  logic [3:0] in1,
  input  logic [1:0] result,
  input  logic [3:0] in0_reg,
  input  logic [3:0] in1_reg
);
  // Use any change as our sampling event
  default clocking cb @(in0 or in1 or result or in0_reg or in1_reg); endclocking

  // Helper: canonical encoding of compare
  function automatic logic [1:0] enc (input logic [3:0] a, b);
    enc = (a > b) ? 2'b01 :
          (a < b) ? 2'b10 :
                    2'b00;
  endfunction

  // Guard for $past on first sample
  bit past_valid;
  initial past_valid = 1'b0;
  always @(in0 or in1 or result or in0_reg or in1_reg) past_valid = 1'b1;

  // Encoding must always be valid and known
  a_valid_encoding: assert property (cb
    !$isunknown(result) && (result inside {2'b00,2'b01,2'b10})
  ) else $error("Invalid result encoding");

  // SPEC (intended): zero-latency comparator on inputs (evaluated after NBA via ##0)
  // This DUT will fail these if it really has a delta-latency bug.
  a_spec_now:  assert property (@(in0 or in1)
    disable iff ($isunknown({in0,in1}))
    ##0 (result == enc(in0,in1))
  ) else $error("Spec fail: result != enc(in0,in1) in same cycle");

  // IMPLEMENTATION (as coded): result follows previous input sample (delta-latency)
  a_impl_delta: assert property (@(in0 or in1)
    disable iff (!past_valid || $isunknown({$past(in0),$past(in1)}))
    ##0 (result == enc($past(in0), $past(in1)))
  ) else $error("Impl fail: result != enc($past(in0),$past(in1))");

  // Result must equal compare of the internal regs (as coded)
  a_match_regs: assert property (cb
    ##0 (result == enc(in0_reg, in1_reg))
  ) else $error("Result != enc(in0_reg,in1_reg)");

  // Internal regs must mirror inputs after the NBA update
  a_regs_follow_inputs: assert property (@(in0 or in1)
    ##0 (in0_reg == in0 && in1_reg == in1)
  ) else $error("in*_reg do not mirror inputs after update");

  // No X-propagation when inputs are known
  a_no_x_when_inputs_known: assert property (cb
    !$isunknown({in0,in1}) |-> !$isunknown(result)
  ) else $error("Unknown result with known inputs");

  // Functional outcome covers
  c_eq:  cover property (@(in0 or in1) ##0 (result == 2'b00));
  c_gt:  cover property (@(in0 or in1) ##0 (result == 2'b01));
  c_lt:  cover property (@(in0 or in1) ##0 (result == 2'b10));

  // Transition covers between distinct outcomes
  c_trans_gt_to_lt: cover property (cb (result==2'b01) ##1 (result==2'b10));
  c_trans_lt_to_gt: cover property (cb (result==2'b10) ##1 (result==2'b01));
  c_trans_to_eq:    cover property (cb (result inside {2'b01,2'b10}) ##1 (result==2'b00));
  c_trans_from_eq:  cover property (cb (result==2'b00) ##1 (result inside {2'b01,2'b10}));

endmodule
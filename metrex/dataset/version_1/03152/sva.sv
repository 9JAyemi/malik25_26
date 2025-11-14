// SVA for add_overflow_detection
// Focus: correctness of 8-bit two’s complement sum and signed-overflow flag.
// Uses ##0 to sample outputs in the postponed region after combinational NBA updates.

`ifndef ADD_OVERFLOW_DETECTION_SVA
`define ADD_OVERFLOW_DETECTION_SVA

module add_overflow_detection_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] s,
  input  logic       overflow
);

  // Canonical expected behaviors
  let sum9       = ({1'b0,a} + {1'b0,b});     // 9-bit unsigned add to capture carry
  let sum8       = sum9[7:0];                 // truncated 8-bit result
  let ovf_expect = (a[7] == b[7]) && (sum8[7] != a[7]); // 2C signed overflow

  // Sum must be correct (bit-accurate truncation of 9-bit add)
  property p_sum_correct;
    @(a or b) disable iff ($isunknown({a,b}))
      1 |-> ##0 (s == sum8);
  endproperty
  assert property (p_sum_correct);

  // Overflow must implement canonical 2C signed-overflow condition
  property p_overflow_correct;
    @(a or b) disable iff ($isunknown({a,b}))
      1 |-> ##0 (overflow == ovf_expect);
  endproperty
  assert property (p_overflow_correct);

  // Outputs must be known when inputs are known
  property p_outputs_known;
    @(a or b) disable iff ($isunknown({a,b}))
      1 |-> ##0 !$isunknown({s,overflow});
  endproperty
  assert property (p_outputs_known);

  // Coverage: exercise both overflow polarities and no-overflow cases
  cover property (@(a or b) disable iff ($isunknown({a,b})) ##0 (ovf_expect && (a[7]==0) && (b[7]==0))); // +/+ overflow
  cover property (@(a or b) disable iff ($isunknown({a,b})) ##0 (ovf_expect && (a[7]==1) && (b[7]==1))); // -/- overflow
  cover property (@(a or b) disable iff ($isunknown({a,b})) ##0 (!ovf_expect));                           // no overflow

  // Boundary sum coverage around 0x7F and 0x80 after truncation
  cover property (@(a or b) ##0 (sum8 == 8'h7F));
  cover property (@(a or b) ##0 (sum8 == 8'h80));

endmodule

// Bind into the DUT
bind add_overflow_detection add_overflow_detection_sva sva_i (
  .a(a),
  .b(b),
  .s(s),
  .overflow(overflow)
);

`endif
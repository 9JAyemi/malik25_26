// SVA for sum_first_last_16_bits
// Bind this file to the DUT.

module sum_first_last_16_bits_sva (
  input logic [31:0] in_signal,
  input logic [15:0] out_signal
);

  default clocking cb @($global_clock); endclocking

  // Helper functions
  function automatic logic [15:0] sum16(input logic [31:0] din);
    return (din[31:16] + din[15:0])[15:0];
  endfunction

  function automatic logic carry_out(input logic [31:0] din);
    logic [16:0] s;
    begin
      s = {1'b0, din[31:16]} + {1'b0, din[15:0]};
      return s[16];
    end
  endfunction

  // Core functional correctness (modulo 2^16), valid when inputs are known
  ap_func: assert property ( !$isunknown(in_signal) |-> (out_signal === sum16(in_signal)) );

  // Zero-latency combinational response on input change
  ap_zero_latency: assert property ( (!$isunknown(in_signal) && $changed(in_signal)) |-> ##0 (out_signal === sum16(in_signal)) );

  // No spurious glitches when input is stable
  ap_stable: assert property ( $stable(in_signal) |-> $stable(out_signal) );

  // No X/Z propagation to output when inputs are 0/1
  ap_no_x: assert property ( !$isunknown(in_signal) |-> !$isunknown(out_signal) );

  // Coverage: carry and no-carry cases
  cv_carry:    cover property ( !$isunknown(in_signal) && carry_out(in_signal) );
  cv_nocarry:  cover property ( !$isunknown(in_signal) && !carry_out(in_signal) );

  // Coverage: output equals one operand when the other is zero
  cv_out_eq_hi: cover property ( (in_signal[15:0]==16'h0)  && (out_signal==in_signal[31:16]) );
  cv_out_eq_lo: cover property ( (in_signal[31:16]==16'h0) && (out_signal==in_signal[15:0]) );

  // Coverage: zero result with non-zero halves (wraparound cancellation)
  cv_zero_wrap: cover property ( (out_signal==16'h0) && (in_signal[31:16]!=16'h0) && (in_signal[15:0]!=16'h0) );

  // Coverage: representative edge patterns
  cv_edge1: cover property ( (in_signal[31:16]==16'hFFFF) && (in_signal[15:0]==16'h0001) && (out_signal==16'h0000) );
  cv_edge2: cover property ( (in_signal[31:16]==16'hAAAA) && (in_signal[15:0]==16'h5555) && (out_signal==16'hFFFF) );

endmodule

bind sum_first_last_16_bits sum_first_last_16_bits_sva sva_i (.*);
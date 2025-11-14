// SVA checker for nios_dut_nios2_gen2_0_cpu_nios2_oci_td_mode
// Focus: functional mapping, zero-latency, independence from unrelated ctrl bits, X-prop, and coverage.

module nios_dut_nios2_gen2_0_cpu_nios2_oci_td_mode_sva (
  input logic [8:0] ctrl,
  input logic [3:0] td_mode
);

  function automatic logic [3:0] decode(input logic [2:0] b);
    case (b)
      3'b000: decode = 4'b0000;
      3'b001: decode = 4'b1000;
      3'b010: decode = 4'b0100;
      3'b011: decode = 4'b1100;
      3'b100: decode = 4'b0010;
      3'b101: decode = 4'b1010;
      3'b110: decode = 4'b0101;
      3'b111: decode = 4'b1111;
      default: decode = 'x;
    endcase
  endfunction

  // Functional decode equivalence (when select bits are known)
  property p_decode_eq;
    !$isunknown(ctrl[7:5]) |-> (td_mode == decode(ctrl[7:5]));
  endproperty
  assert property (@(ctrl or td_mode) p_decode_eq);

  // Zero-latency: td_mode reflects new select in the same delta
  property p_zero_latency;
    (!$isunknown(ctrl[7:5]) && $changed(ctrl[7:5])) |-> ##0 (td_mode == decode(ctrl[7:5]));
  endproperty
  assert property (@(ctrl) p_zero_latency);

  // Independence: td_mode does not depend on ctrl[8] or ctrl[4:0]
  property p_independent_other_bits;
    ($changed({ctrl[8],ctrl[4:0]}) && $stable(ctrl[7:5])) |-> ##0 $stable(td_mode);
  endproperty
  assert property (@(ctrl) p_independent_other_bits);

  // No X on output when select bits are known
  assert property (@(ctrl or td_mode) !$isunknown(ctrl[7:5]) |-> !$isunknown(td_mode));

  // Defensive: td_mode must be one of the 8 legal values
  assert property (@(td_mode) 1 |-> (td_mode inside {
    4'b0000,4'b1000,4'b0100,4'b1100,4'b0010,4'b1010,4'b0101,4'b1111
  }));

  // Coverage: observe each mapping at least once
  cover property (@(ctrl) (ctrl[7:5]==3'b000 && td_mode==4'b0000));
  cover property (@(ctrl) (ctrl[7:5]==3'b001 && td_mode==4'b1000));
  cover property (@(ctrl) (ctrl[7:5]==3'b010 && td_mode==4'b0100));
  cover property (@(ctrl) (ctrl[7:5]==3'b011 && td_mode==4'b1100));
  cover property (@(ctrl) (ctrl[7:5]==3'b100 && td_mode==4'b0010));
  cover property (@(ctrl) (ctrl[7:5]==3'b101 && td_mode==4'b1010));
  cover property (@(ctrl) (ctrl[7:5]==3'b110 && td_mode==4'b0101));
  cover property (@(ctrl) (ctrl[7:5]==3'b111 && td_mode==4'b1111));

  // Coverage: unrelated ctrl bits toggle without affecting td_mode
  cover property (@(ctrl) ($changed({ctrl[8],ctrl[4:0]}) && $stable(ctrl[7:5])) ##0 $stable(td_mode));

endmodule

// Bind into the DUT
bind nios_dut_nios2_gen2_0_cpu_nios2_oci_td_mode
  nios_dut_nios2_gen2_0_cpu_nios2_oci_td_mode_sva
    td_mode_sva_i(.ctrl(ctrl), .td_mode(td_mode));
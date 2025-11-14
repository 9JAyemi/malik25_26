// SVA for VCO_interface
// Bind this to the DUT to check key behavior and provide concise coverage.

module VCO_interface_sva #(
  parameter int unsigned fmin = 1,
  parameter int unsigned fmax = 1000,
  parameter int unsigned vmin = 0,
  parameter int unsigned vmax = 255
) (
  input logic             in,
  input logic [7:0]       vctrl,
  input logic             out,
  input logic [31:0]      count,
  input logic [31:0]      freq
);

  function automatic int unsigned map_vctrl(input logic [7:0] v);
    map_vctrl = (int'(v) - vmin) * (fmax - fmin) / (vmax - vmin) + fmin;
  endfunction

  default clocking cb @(posedge in); endclocking
  default disable iff ($isunknown({in, vctrl, out, count, freq}));

  // freq mapping and bounds
  a_freq_map:    assert property (freq == map_vctrl(vctrl));
  a_freq_bounds: assert property (freq >= fmin && freq <= fmax && freq > 0);

  // Monotonicity of mapping (non-decreasing with vctrl)
  a_freq_mono_inc: assert property ($rose(1'b1) |-> ($past(vctrl) <= vctrl) |-> ($past(freq) <= freq));

  // Toggle protocol (based on the DUT's nonblocking semantics: cond uses past values)
  localparam bit UNUSED = 1'b0;
  a_toggle_when:      assert property ( ($past(count) >= $past(freq)) |=> (out != $past(out)) );
  a_no_spurious_tgl:  assert property ( !($past(count) >= $past(freq)) |=> $stable(out) );

  // Count update rules
  a_count_reset_on_tgl: assert property ( ($past(count) >= $past(freq)) |=> (count == 32'd0) );
  a_count_inc_else:     assert property ( !($past(count) >= $past(freq)) |=> (count == $past(count) + 32'd1) );

  // Period check when freq is stable: next toggle occurs exactly after freq+1 cycles
  property p_period_stable_freq;
    int unsigned k;
    (out != $past(out), k = freq) |=> ($stable(out) && freq == k) [*k] ##1 (out != $past(out) && freq == k);
  endproperty
  a_period_stable: assert property (p_period_stable_freq);

  // Coverage
  c_any_toggle:      cover property (out != $past(out));
  c_min_freq_toggle: cover property ((freq == fmin) ##1 (out != $past(out)));
  c_max_freq_toggle: cover property ((freq == fmax) ##1 (out != $past(out)));
  c_count_wrap:      cover property ( ($past(count) >= $past(freq)) |=> (count == 0) );

endmodule

// Bind to DUT (connects to internal regs)
bind VCO_interface VCO_interface_sva #(
  .fmin(fmin), .fmax(fmax), .vmin(vmin), .vmax(vmax)
) vco_if_sva (
  .in(in), .vctrl(vctrl), .out(out), .count(count), .freq(freq)
);
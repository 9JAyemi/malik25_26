// SVA for lpm_inv: concise, high-quality checks and coverage
module lpm_inv_sva #(parameter int lpm_width = 1)
(
  input  logic [lpm_width-1:0] data,
  input  logic [lpm_width-1:0] result
);

  // Static/elaboration checks
  initial begin
    assert (lpm_width > 0) else $error("lpm_width must be > 0");
    assert ($bits(data)   == lpm_width) else $error("$bits(data) != lpm_width");
    assert ($bits(result) == lpm_width) else $error("$bits(result) != lpm_width");
  end

  // Result must always be bitwise inversion of data (allowing X/Z propagation)
  property p_comb_correct;
    @(data or result) ##0 (result === ~data);
  endproperty
  assert property (p_comb_correct);

  // On any data change, result must settle (after delta) to ~data
  property p_update_on_data_change;
    @(data) ##0 (result === ~data);
  endproperty
  assert property (p_update_on_data_change);

  // Result must not change unless data changed
  property p_no_spurious_result_change;
    @(data or result) $changed(result) |-> $changed(data);
  endproperty
  assert property (p_no_spurious_result_change);

  // If input is fully known, output must be fully known (no unexpected X/Z)
  property p_no_unknown_output_when_input_known;
    @(data or result) !$isunknown(data) |-> !$isunknown(result);
  endproperty
  assert property (p_no_unknown_output_when_input_known);

  // Per-bit edge correctness and coverage
  genvar i;
  generate
    for (i = 0; i < lpm_width; i++) begin : g_bit
      // Rising edge on data[i] implies falling edge on result[i] (after delta)
      property p_bit_rise_fall;
        @(data[i]) $rose(data[i]) |-> ##0 $fell(result[i]);
      endproperty
      assert property (p_bit_rise_fall);

      // Falling edge on data[i] implies rising edge on result[i] (after delta)
      property p_bit_fall_rise;
        @(data[i]) $fell(data[i]) |-> ##0 $rose(result[i]);
      endproperty
      assert property (p_bit_fall_rise);

      // Coverage: observe both edge relationships
      cover property (@(data[i]) $rose(data[i]) ##0 $fell(result[i]));
      cover property (@(data[i]) $fell(data[i]) ##0 $rose(result[i]));
    end
  endgenerate

  // Coverage: see all-zeros and all-ones inputs at least once
  cover property (@(data) data == '0);
  cover property (@(data) data == '1);

endmodule

// Bind into the DUT
bind lpm_inv lpm_inv_sva #(.lpm_width(lpm_width)) (.data(data), .result(result));
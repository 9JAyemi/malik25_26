// SVA checker for AGC
// - Purely combinational checks with zero-delay settle (##0)
// - Uses only SVA/immediate assertions; no DUT changes

module AGC_sva #(parameter gain_bits = 8)
(
  input  logic [15:0]                input_signal,
  input  logic [7:0]                 control_signal,
  input  logic [15:0]                output_signal,
  // Internal DUT signals (bound hierarchically)
  input  logic [gain_bits-1:0]       gain_value,
  input  logic [15:0]                adjusted_signal
);

  // Golden gain mapping (mirror of DUT adjust_gain)
  function automatic [gain_bits-1:0] expected_gain (input logic [7:0] control);
    case (control)
      8'h00: expected_gain = 8'h00;
      8'h01: expected_gain = 8'h01;
      8'h02: expected_gain = 8'h02;
      8'h03: expected_gain = 8'h03;
      8'h04: expected_gain = 8'h04;
      8'h05: expected_gain = 8'h05;
      8'h06: expected_gain = 8'h06;
      8'h07: expected_gain = 8'h07;
      8'h08: expected_gain = 8'h08;
      8'h09: expected_gain = 8'h09;
      8'h0A: expected_gain = 8'h0A;
      8'h0B: expected_gain = 8'h0B;
      8'h0C: expected_gain = 8'h0C;
      8'h0D: expected_gain = 8'h0D;
      8'h0E: expected_gain = 8'h0E;
      8'h0F: expected_gain = 8'h0F;
      8'h10: expected_gain = 8'h10;
      8'h11: expected_gain = 8'h11;
      8'h12: expected_gain = 8'h12;
      8'h13: expected_gain = 8'h13;
      8'h14: expected_gain = 8'h14;
      8'h15: expected_gain = 8'h15;
      8'h16: expected_gain = 8'h16;
      8'h17: expected_gain = 8'h17;
      8'h18: expected_gain = 8'h18;
      default: expected_gain = 8'h00;
    endcase
  endfunction

  // Utilities
  function automatic bit known(input logic [0:0] dummy, input logic [$bits(dummy)-1:0] unused); return 1'b1; endfunction
  // Known-value guard (compact)
  function automatic bit is_known(input logic [$bits({input_signal,control_signal})-1:0] v); return !$isunknown(v); endfunction

  // 1) No X/Z on outputs when inputs are known
  property p_no_x;
    @(input_signal or control_signal)
      is_known({input_signal,control_signal}) |-> ##0 !$isunknown({gain_value, adjusted_signal, output_signal});
  endproperty
  assert property (p_no_x);

  // 2) Gain map is combinationally correct
  property p_gain_map;
    @(control_signal)
      !$isunknown(control_signal) |-> ##0 (gain_value === expected_gain(control_signal));
  endproperty
  assert property (p_gain_map);

  // 3) adjusted_signal computes input_signal * gain_value (truncated to 16 bits)
  property p_adjusted_compute;
    @(input_signal or gain_value)
      !$isunknown({input_signal,gain_value}) |-> ##0 (adjusted_signal === (input_signal * gain_value)[15:0]);
  endproperty
  assert property (p_adjusted_compute);

  // 4) output_signal mirrors adjusted_signal
  property p_output_assign;
    @(adjusted_signal)
      !$isunknown(adjusted_signal) |-> ##0 (output_signal === adjusted_signal);
  endproperty
  assert property (p_output_assign);

  // 5) End-to-end check: output equals input * expected_gain(control)
  property p_e2e;
    @(input_signal or control_signal)
      !$isunknown({input_signal,control_signal}) |-> ##0 (output_signal === (input_signal * expected_gain(control_signal))[15:0]);
  endproperty
  assert property (p_e2e);

  // 6) Optional overflow detection (upper 8 bits of 24-bit product nonzero)
  //    Flag as warning to highlight potential truncation loss
  property p_overflow_trunc;
    @(input_signal or control_signal)
      !$isunknown({input_signal,control_signal}) |-> ##0 ((input_signal * expected_gain(control_signal))[23:16] == 8'h00);
  endproperty
  assert property (p_overflow_trunc)
    else $warning("AGC: product overflow truncated (upper bits nonzero)");

  // Coverage
  // - Hit every defined control code 0x00..0x18
  genvar cv;
  generate
    for (cv = 8'h00; cv <= 8'h18; cv++) begin : C_CTRL_DEFINED
      cover property (@(control_signal) control_signal == cv[7:0]);
    end
  endgenerate

  // - Hit at least one default case (outside 0x00..0x18)
  cover property (@(control_signal) !(control_signal inside {[8'h00:8'h18]}));

  // - Exercise zero and max input
  cover property (@(input_signal) input_signal == 16'h0000);
  cover property (@(input_signal) input_signal == 16'hFFFF);

  // - Observe an overflow/truncation event
  cover property (@(input_signal or control_signal)
                    ((input_signal * expected_gain(control_signal))[23:16] != 8'h00));

endmodule

// Bind into all AGC instances; connects internals for stronger checks
bind AGC AGC_sva #(.gain_bits(gain_bits)) AGC_sva_i (
  .input_signal    (input_signal),
  .control_signal  (control_signal),
  .output_signal   (output_signal),
  .gain_value      (gain_value),
  .adjusted_signal (adjusted_signal)
);
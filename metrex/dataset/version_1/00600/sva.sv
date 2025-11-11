// SVA for touch_sensor
module touch_sensor_sva #(parameter int n=4, m=2) (
  input logic                   clk,
  input logic [n-1:0]           touch_sensors,
  input logic [m-1:0]           digital_outputs,
  input logic [n-1:0]           touch_sensors_prev,
  input logic [m-1:0]           digital_outputs_curr,
  input logic [m-1:0]           digital_outputs_prev
);

  // Param checks
  initial begin
    assert (n > 0 && m > 0)
      else $fatal(1, "n and m must be > 0 (n=%0d m=%0d)", n, m);
    if (m != n)
      $warning("Width mismatch: m(%0d) != n(%0d). Outputs will be %s of XOR.",
               m, n, (m < n) ? "LSB truncation" : "zero-extension");
  end

  // Clock, past-valid
  default clocking cb @(posedge clk); endclocking
  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Map XOR result to m bits (truncate or zero-extend)
  function automatic logic [m-1:0] map_xor(input logic [n-1:0] a, input logic [n-1:0] b);
    logic [m-1:0] r;
    if (m <= n) r = (a ^ b)[m-1:0];
    else begin
      r = '0;
      r[n-1:0] = (a ^ b);
    end
    return r;
  endfunction

  // Combinational correctness of digital_outputs_curr
  always @* begin
    assert (digital_outputs_curr == map_xor(touch_sensors, touch_sensors_prev))
      else $error("digital_outputs_curr != (touch_sensors ^ touch_sensors_prev) mapped to m bits");
  end

  // Pipeline/registering checks
  // touch_sensors_prev tracks previous touch_sensors
  assert property (disable iff (!past_valid)
                   touch_sensors_prev == $past(touch_sensors))
    else $error("touch_sensors_prev mismatch");

  // Functional spec: registered digital_outputs equals XOR of current and previous inputs
  assert property (disable iff (!past_valid)
                   digital_outputs == map_xor(touch_sensors, $past(touch_sensors)))
    else $error("digital_outputs functional mismatch");

  // Optional: prev register mirrors curr at previous cycle
  assert property (disable iff (!past_valid)
                   digital_outputs_prev == $past(digital_outputs_curr))
    else $error("digital_outputs_prev mismatch");

  // No-change => zero output
  assert property (disable iff (!past_valid)
                   (touch_sensors == $past(touch_sensors)) |-> (digital_outputs == '0))
    else $error("Output not zero when no input change");

  // X-propagation safety: if inputs known this and last cycle, output must be known
  assert property (disable iff (!past_valid)
                   (!$isunknown(touch_sensors) && !$isunknown($past(touch_sensors))) |-> !$isunknown(digital_outputs))
    else $error("X/Z observed on digital_outputs with known inputs");

  // If m > n, upper extension bits must be zero
  if (m > n) begin
    assert property (disable iff (!past_valid) digital_outputs[m-1:n] == '0)
      else $error("Upper extended bits of digital_outputs not zero");
  end

  // Coverage
  // No-change -> zero output
  cover property (disable iff (!past_valid)
                  (touch_sensors == $past(touch_sensors)) && (digital_outputs == '0));

  // Single-bit pulse on each output bit when exactly one input bit toggles
  sequence one_bit_change(int i);
    (touch_sensors[i] != $past(touch_sensors[i])) &&
    $onehot(touch_sensors ^ $past(touch_sensors));
  endsequence

  property one_bit_pulse(int i);
    disable iff (!past_valid)
    one_bit_change(i) |-> digital_outputs[i] ##1
    (touch_sensors == $past(touch_sensors) && digital_outputs == '0);
  endproperty

  genvar i;
  generate
    for (i = 0; i < m; i++) begin : COV_ONEBIT
      cover property (one_bit_pulse(i));
    end
  endgenerate

  // Multi-bit change observed at outputs
  cover property (disable iff (!past_valid)
                  ($countones(touch_sensors ^ $past(touch_sensors)) >= 2) && (digital_outputs != '0));

endmodule

// Bind to DUT (assumes internal signal names from the provided RTL)
bind touch_sensor
  touch_sensor_sva #(.n(n), .m(m)) touch_sensor_sva_i (
    .clk                (clk),
    .touch_sensors      (touch_sensors),
    .digital_outputs    (digital_outputs),
    .touch_sensors_prev (touch_sensors_prev),
    .digital_outputs_curr(digital_outputs_curr),
    .digital_outputs_prev(digital_outputs_prev)
  );
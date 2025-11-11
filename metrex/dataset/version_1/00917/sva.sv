// SVA for DLL: concise, high-quality checks and coverage
// Bind these assertions to the DLL instance.

module dll_sva #(
  parameter int DELAY_TIME = 10
)(
  input  logic                         clk,
  input  logic                         rst,
  input  logic                         in,
  input  logic                         out,
  input  logic [DELAY_TIME-1:0]        delay_line,
  input  logic [1:0]                   phase_detector_out,
  input  logic [DELAY_TIME-1:0]        delay_time_reg
);

  // Basic parameter sanity
  initial begin
    assert (DELAY_TIME >= 2)
      else $error("DLL: DELAY_TIME must be >= 2");
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (checks only when rst is asserted)
  assert property (@(posedge clk)
    rst |-> (delay_line == '0 && phase_detector_out == 2'b00 && delay_time_reg == DELAY_TIME))
    else $error("DLL reset values mismatch");

  // Shift-register behavior
  assert property (delay_line == { $past(in), $past(delay_line[DELAY_TIME-1:1]) })
    else $error("DLL delay_line shift incorrect");

  // Phase detector correctness
  assert property (
    phase_detector_out
      == ({ $past(delay_line[DELAY_TIME-1]), $past(delay_line[DELAY_TIME-2]) }
          ^ { $past(in), $past(delay_line[DELAY_TIME-1]) }))
    else $error("DLL phase_detector_out incorrect");

  // Delay-time register update semantics (based on previous pd_out)
  assert property ($past(phase_detector_out) == 2'b01
                   |-> delay_time_reg == $past(delay_time_reg) + 1)
    else $error("DLL delay_time_reg increment incorrect");

  assert property ($past(phase_detector_out) == 2'b10
                   |-> delay_time_reg == $past(delay_time_reg) - 1)
    else $error("DLL delay_time_reg decrement incorrect");

  assert property (($past(phase_detector_out) inside {2'b00,2'b11})
                   |-> delay_time_reg == $past(delay_time_reg))
    else $error("DLL delay_time_reg should hold when pd_out is 00/11");

  // Safety: index range for variable bit-select and safe updates at boundaries
  assert property (delay_time_reg inside {[1:DELAY_TIME]})
    else $error("DLL delay_time_reg out of valid range [1:DELAY_TIME]");

  assert property ($past(phase_detector_out) == 2'b01 |-> $past(delay_time_reg) <  DELAY_TIME)
    else $error("DLL increment would overflow valid range");

  assert property ($past(phase_detector_out) == 2'b10 |-> $past(delay_time_reg) >  1)
    else $error("DLL decrement would underflow valid range");

  // Output must mirror the selected tap from the previous cycle
  // Generate one assertion per possible index to avoid dynamic-index-in-$past issues
  genvar k;
  generate
    for (k = 1; k <= DELAY_TIME; k++) begin : g_out_map
      assert property ($past(delay_time_reg) == k |-> out == $past(delay_line[k-1]))
        else $error("DLL out mismatch for index %0d", k);
    end
  endgenerate

  // No X-propagation after reset deassertion on key observables
  assert property (!$isunknown({delay_time_reg, phase_detector_out, out})))
    else $error("DLL unknown (X/Z) detected on key signals");

  // Coverage: observe both PD directions and boundary hits
  cover property (phase_detector_out == 2'b01);
  cover property (phase_detector_out == 2'b10);
  cover property (delay_time_reg == 1);
  cover property (delay_time_reg == DELAY_TIME);

endmodule

// Bind to DUT
bind DLL dll_sva #(.DELAY_TIME(delay_time)) dll_sva_i (
  .clk              (clk),
  .rst              (rst),
  .in               (in),
  .out              (out),
  .delay_line       (delay_line),
  .phase_detector_out(phase_detector_out),
  .delay_time_reg   (delay_time_reg)
);
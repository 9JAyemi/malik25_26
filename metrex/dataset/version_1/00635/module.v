
module PLL (
  input  ref_clk,
  input  ctrl,
  output synth_clk
);

parameter m = 10; // multiplication factor
parameter f_ref = 100000; // reference clock frequency
parameter f_out = 1000000; // output frequency

reg [31:0] phase_accumulator;
reg [31:0] feedback_clk_counter;
reg [31:0] reference_clk_counter;

wire feedback_clk;
wire phase_difference;
wire loop_filter_output;

// Divide the reference clock frequency by multiplication factor 'm' to get the frequency of the feedback signal.
assign feedback_clk = feedback_clk_counter == (f_ref / m - 1);
always @(posedge ref_clk) begin
  if (feedback_clk) begin
    feedback_clk_counter <= 0;
  end else begin
    feedback_clk_counter <= feedback_clk_counter + 1;
  end
end

// Compare the phase of the reference and feedback signals using a phase detector.
phase_detector pd(
  .ref_clk(ref_clk),
  .feedback_clk(feedback_clk),
  .phase_difference(phase_difference)
);

// Adjust the frequency of the controlled oscillator based on the phase difference using a loop filter.
loop_filter lf(
  .ctrl(ctrl),
  .phase_difference(phase_difference),
  .loop_filter_output(loop_filter_output)
);

// Multiply the frequency of the controlled oscillator by multiplication factor 'm' to get the frequency of the synthesized clock signal.
reg synth_clk_reg;
always @(negedge ref_clk) begin
  if (phase_accumulator < m) begin
    phase_accumulator <= phase_accumulator + (f_out * m) / f_ref;
    synth_clk_reg <= ~synth_clk_reg;
  end else begin
    phase_accumulator <= 0;
  end
end

assign synth_clk = synth_clk_reg;

endmodule
module phase_detector (
  input ref_clk,
  input feedback_clk,
  output phase_difference
);

reg ref_clk_last;
reg feedback_clk_last;

always @(negedge ref_clk) begin
  ref_clk_last <= ref_clk;
end

always @(negedge feedback_clk) begin
  feedback_clk_last <= feedback_clk;
end

assign phase_difference = feedback_clk_last ^ ref_clk_last;

endmodule
module loop_filter (
  input ctrl,
  input phase_difference,
  output loop_filter_output
);

reg [31:0] integrator;

parameter kp = 1;
parameter ki = 1;

always @(negedge ctrl) begin
  integrator <= integrator + phase_difference;
end

assign loop_filter_output = integrator * ki;

endmodule
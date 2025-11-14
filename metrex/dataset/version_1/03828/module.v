
module freq_syn (
  input clk_ref,
  input [7:0] ctrl,
  output reg clk_syn
);

parameter n = 8; // number of bits in the digital control signal
parameter f_ref = 10_000_000; // frequency of the reference clock signal (in Hz)
parameter f_min = 1_000_000; // minimum output frequency of the synthesizer (in Hz)
parameter f_max = 100_000_000; // maximum output frequency of the synthesizer (in Hz)

reg [7:0] ctrl_reg; // register for storing the digital control signal
reg [31:0] phase_accum; // register for storing the phase accumulator value
reg [31:0] phase_inc; // register for storing the phase increment value
reg [31:0] phase_err; // register for storing the phase error value
reg [31:0] phase_err_int; // register for storing the integrated phase error value
reg [31:0] vco_ctrl; // register for storing the VCO control voltage value
reg [31:0] vco_freq; // register for storing the VCO frequency value
reg [32:0] phase_syn; // register for storing the synthesized phase value

wire [32:0] phase_ref; // wire for storing the reference phase value
wire [32:0] phase_diff; // wire for storing the phase difference value
wire [32:0] phase_err_filt; // wire for storing the filtered phase error value
wire [32:0] phase_err_integ; // wire for storing the integrated phase error value
wire [32:0] vco_ctrl_filt; // wire for storing the filtered VCO control voltage value
wire [32:0] vco_freq_div; // wire for storing the divided VCO frequency value

// generate the reference phase value
assign phase_ref = (f_ref * 33'h1_0000_0000) / (2 * f_max);

// generate the phase increment value
always @(*) begin
  phase_inc = (ctrl_reg * (33'h1_0000_0000 - phase_ref)) / (2**n);
end

// generate the synthesized phase value
always @(posedge clk_ref) begin
  phase_accum <= phase_accum + phase_inc;
  phase_syn <= phase_accum + phase_err_int;
end

// generate the phase difference value
assign phase_diff = phase_ref - phase_syn;


// generate the integrated phase error value
always @(posedge clk_ref) begin
  if (phase_err_int >= 0) begin
    phase_err_int <= phase_err_int + phase_err_filt;
  end else begin
    phase_err_int <= phase_err_int - phase_err_filt;
  end
end


// generate the divided VCO frequency value
assign vco_freq_div = vco_freq / (2**16);

// generate the synthesized clock signal
always @(posedge clk_ref) begin
  vco_freq <= vco_ctrl_filt;
  clk_syn <= ~clk_syn;
end

// register the digital control signal
always @(posedge clk_ref) begin
  ctrl_reg <= ctrl;
end

endmodule
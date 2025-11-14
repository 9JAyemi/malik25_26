module CDR (
  input data,
  input ref_clk,
  output clk_out
);

parameter data_rate = 10e9; // data rate in bits per second
parameter ref_clk_rate = 20e9; // frequency of reference clock signal in Hz
parameter lock_threshold = 0.1; // threshold value for phase detector

reg data_reg;
reg ref_clk_reg;
reg [1:0] phase_error;
reg [31:0] filter_out;
reg [31:0] vco_out;

wire phase_error_sign;
wire [31:0] filter_in;
wire [31:0] vco_in;

assign phase_error_sign = phase_error[1];
assign filter_in = phase_error_sign ? -phase_error : phase_error;
assign vco_in = filter_out;

always @(posedge ref_clk) begin
  data_reg <= data;
  ref_clk_reg <= ref_clk;
end

always @(posedge ref_clk) begin
  phase_error <= {phase_error[0], data_reg ^ ref_clk_reg};
end

always @(posedge ref_clk) begin
  filter_out <= filter_out + ((filter_in - filter_out) >> 4);
end

always @(posedge ref_clk) begin
  vco_out <= vco_out + ((vco_in - vco_out) >> 8);
end

assign clk_out = vco_out[31];

endmodule
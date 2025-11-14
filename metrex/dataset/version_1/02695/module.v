
module freq_synthesizer (
  input ref_clk,
  input [n-1:0] ctrl,
  output reg syn_clk
);

parameter n = 4; // number of control signals
parameter m = 8; // number of output signals
parameter f_out = 100000000; // desired output frequency (100 MHz)
parameter f_ref = 25000000; // frequency of reference clock signal (25 MHz)

reg [m-1:0] counter;
reg [n-1:0] divider;
reg [n-1:0] phase;
reg [n-1:0] phase_accumulator;
reg [n-1:0] phase_increment;
reg [n-1:0] phase_accumulator_next;

wire [n-1:0] ctrl_scaled;
wire [n-1:0] ctrl_scaled_inv;
wire [n-1:0] ctrl_scaled_int;
wire [n-1:0] ctrl_scaled_frac;

// Calculate scaled control signals
assign ctrl_scaled = $signed(ctrl) * ($signed(f_out) / $signed(f_ref));
assign ctrl_scaled_inv = ($signed(f_out) / $signed(f_ref)) - ctrl_scaled;
assign ctrl_scaled_int = ctrl_scaled[n-1:0];
assign ctrl_scaled_frac = ctrl_scaled - ctrl_scaled_int;

// Clock divider
always @ (posedge ref_clk) begin
  if (counter == 0) begin
    phase_accumulator <= phase_accumulator_next;
    counter <= divider;
  end else begin
    counter <= counter - 1;
  end
end

// Phase increment calculation
always @ (posedge ref_clk) begin
  phase_increment <= ctrl_scaled_int + (ctrl_scaled_frac > phase_accumulator);
end

// Phase accumulator
always @ (posedge ref_clk) begin
  phase_accumulator_next <= phase_accumulator + phase_increment;
end

// Output clock generation
always @ (posedge ref_clk) begin
  if (phase_accumulator_next >= (f_out / f_ref)) begin
    syn_clk <= ~syn_clk;
  end
end

// Divider calculation
always @ (ctrl_scaled_int, ctrl_scaled_frac) begin
  divider <= (f_out / f_ref) / (ctrl_scaled_int + ctrl_scaled_frac);
end

endmodule
module cic_filter #(
  parameter N = 3, // order of filter
  parameter R = 4, // decimation or interpolation factor
  parameter M = 16 // number of bits in input signal
) (
  input [M-1:0] in,
  input clk,
  input rst,
  output [M-1:0] out
);

reg [M-1:0] integrator_reg = 0; // accumulator for integrator
reg [M-1:0] comb_reg [0:N-1]; // shift register for comb filter
reg [M-1:0] decimator_reg = 0; // register for decimator
reg [M-1:0] interpolator_reg = 0; // register for interpolator
reg [M-1:0] out_reg = 0; // register for output

integer i;

always @(posedge clk) begin
  if (rst) begin
    integrator_reg <= 0;
    for (i = 0; i < N; i = i + 1) begin
      comb_reg[i] <= 0;
    end
    decimator_reg <= 0;
    interpolator_reg <= 0;
    out_reg <= 0;
  end else begin
    // integrator
    integrator_reg <= integrator_reg + in;
    
    // comb filter
    comb_reg[0] <= integrator_reg;
    for (i = 1; i < N; i = i + 1) begin
      comb_reg[i] <= comb_reg[i-1];
    end
    
    // decimator or interpolator
    if (R > 1) begin
      decimator_reg <= decimator_reg + 1;
      if (decimator_reg == R-1) begin
        out_reg <= comb_reg[N-1];
        decimator_reg <= 0;
      end
    end else begin
      interpolator_reg <= interpolator_reg + 1;
      if (interpolator_reg == R-1) begin
        out_reg <= comb_reg[N-1];
        interpolator_reg <= 0;
      end
    end
  end
end

assign out = out_reg;

endmodule
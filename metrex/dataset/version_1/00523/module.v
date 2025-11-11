module CIC #(
  parameter n = 2, // number of input signals
  parameter m = 2, // number of output signals
  parameter r = 2, // decimation rate
  parameter N = 2 // filter order
)(
  input [n-1:0] in,
  output [m-1:0] out,
  input clk // Clock signal
);


// Decimation Stage
reg [n-1:0] decimated_input;
reg [7:0] counter; // counter for decimation
always @(posedge clk) begin
  if (counter == r-1) begin
    decimated_input <= in;
    counter <= 0;
  end else begin
    counter <= counter + 1;
  end
end

// Integrator Stage
reg [n-1:0] integrator_input;
reg [n-1:0] integrator_output;
always @(posedge clk) begin
  integrator_input <= decimated_input;
  integrator_output <= integrator_output + integrator_input;
end

// Comb Stage
reg [n-1:0] comb_input;
reg [n-1:0] comb_output;
always @(posedge clk) begin
  comb_input <= integrator_output;
  comb_output <= comb_input - comb_output;
end

// Output
assign out = comb_output;

endmodule
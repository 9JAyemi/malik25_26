module manchester_encoder (
  input clk,
  input [n-1:0] in,
  output [m-1:0] out
);

parameter n = 4; // number of input signals
parameter m = 2; // number of output signals
parameter freq = 100; // clock frequency in MHz
parameter data_rate = 10; // data rate in Mbps

// implementation of Manchester encoder
reg [n-1:0] prev_in;
always @(posedge clk) begin
  prev_in <= in;
end

assign out = (prev_in ^ in) ? {1'b1, 1'b0} : {1'b0, 1'b1};

endmodule

module manchester_decoder (
  input clk,
  input [n-1:0] in,
  output [m-1:0] out
);

parameter n = 4; // number of input signals
parameter m = 2; // number of output signals
parameter freq = 100; // clock frequency in MHz
parameter data_rate = 10; // data rate in Mbps

// implementation of Manchester decoder
reg [n-1:0] prev_in;
always @(posedge clk) begin
  prev_in <= in;
end

assign out = (prev_in ^ in) ? 1'b1 : 1'b0;

endmodule
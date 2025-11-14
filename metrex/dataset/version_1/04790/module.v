module CDC_synchronizer #(
  parameter n = 8, // number of bits in the data signal
  parameter t = 2 // number of clock cycles for synchronization
)(
  input wire clk_in,
  input wire rst_in,
  input wire [n-1:0] data_in,
  output reg [n-1:0] data_out
);


reg [n-1:0] ff1_out;
reg [n-1:0] ff2_out;

wire enable;

assign enable = ~(&{clk_in, rst_in});

always @(posedge clk_in) begin
  ff1_out <= data_in;
end

integer i;
always @(posedge clk_in) begin // Changed clk_out to clk_in
  if (i < t) begin
    i <= i + 1;
  end else begin
    ff2_out <= ff1_out;
    i <= 0;
  end
end

always @(posedge clk_in) begin // Changed clk_out to clk_in
  if (enable) begin
    data_out <= ff2_out;
  end
end

endmodule
module crc_generator_checker #(
  parameter data_width = 8,
  parameter crc_width = 16
) (
  input [data_width-1:0] data_in,
  input [crc_width-1:0] crc_in,
  input reset,
  input clk,
  output [crc_width-1:0] crc_out,
  output error
);


reg [crc_width-1:0] crc_reg;
reg [data_width-1:0] data_reg;
reg [crc_width-1:0] crc_gen;
reg [crc_width-1:0] crc_check;

wire [crc_width-1:0] crc_out_int;
wire [crc_width-1:0] crc_in_shifted;
wire [data_width-1:0] data_in_shifted;
wire [crc_width-1:0] crc_gen_shifted;
wire [crc_width-1:0] crc_check_shifted;
wire error_temp;

assign crc_out = crc_out_int;
assign error = error_temp;

// Shift register for input data
always @(posedge clk) begin
  if (reset) begin
    data_reg <= 0;
  end else begin
    data_reg <= {data_reg[data_width-2:0], data_in};
  end
end

// Shift register for input CRC
always @(posedge clk) begin
  if (reset) begin
    crc_check <= 0;
  end else begin
    crc_check <= crc_in_shifted;
  end
end

// Shift register for generated CRC
always @(posedge clk) begin
  if (reset) begin
    crc_gen <= 0;
  end else begin
    crc_gen <= crc_gen_shifted;
  end
end

// Shift register for shifted input data
assign data_in_shifted = {data_reg[data_width-2:0], data_in};

// Shift register for shifted input CRC
assign crc_in_shifted = {crc_check[crc_width-2:0], crc_check};

// Shift register for shifted generated CRC
assign crc_gen_shifted = {crc_gen[crc_width-2:0], crc_gen};

// Calculation of CRC checksum
always @(posedge clk) begin
  if (reset) begin
    crc_reg <= 0;
  end else begin
    crc_reg <= crc_gen_shifted ^ crc_in_shifted ^ data_in_shifted;
  end
end

// Error detection
assign error_temp = (crc_check_shifted != crc_out_int);

// Shift register for shifted checked CRC
assign crc_check_shifted = {crc_check_shifted[crc_width-2:0], crc_check};

assign crc_out_int = crc_reg;

endmodule
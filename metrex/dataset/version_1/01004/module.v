module adler_checksum #(
  parameter data_width = 8,
  parameter prime = 65521

)(
  input clk,
  input reset,
  input [data_width-1:0] data_in,
  input valid_in,
  input start,
  input [data_width-1:0] checksum_in, // Only for checker
  output [data_width-1:0] data_out,
  output valid_out,
  output [data_width-1:0] checksum_out, // Only for generator
  output checksum_match
);


reg [data_width-1:0] data_reg;
reg [data_width-1:0] checksum_reg;
reg [data_width-1:0] sum_reg;
reg [data_width-1:0] sum_of_squares_reg;
reg [data_width-1:0] checksum_calc;
reg [data_width-1:0] checksum_match_reg;

assign data_out = data_reg;
assign valid_out = valid_in;
assign checksum_out = checksum_reg;
assign checksum_match = checksum_match_reg;

always @(posedge clk) begin
  if (reset) begin
    data_reg <= 0;
    checksum_reg <= 0;
    sum_reg <= 0;
    sum_of_squares_reg <= 0;
    checksum_calc <= 0;
    checksum_match_reg <= 0;
  end else begin
    if (valid_in) begin
      data_reg <= data_in;
      sum_reg <= sum_reg + data_in;
      sum_of_squares_reg <= sum_of_squares_reg + (data_in * data_in);
    end
    if (start) begin
      checksum_reg <= (sum_of_squares_reg * 65536) + sum_reg;
      checksum_reg <= checksum_reg % prime;
      if (checksum_in != 0) begin // Checker mode
        if (checksum_in == checksum_reg) begin
          checksum_match_reg <= 1;
        end else begin
          checksum_match_reg <= 0;
        end
      end else begin // Generator mode
        checksum_calc <= checksum_reg;
      end
    end
  end
end

endmodule
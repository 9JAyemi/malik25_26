module shift_data(
  input [15:0] data_in,
  input [3:0] ctrl,
  output [15:0] data_out
);

  reg [15:0] shifted_data;

  always @(*) begin
    case(ctrl)
      4'b0000: shifted_data = data_in;
      4'b0001: shifted_data = {data_in[14:0], 1'b0};
      4'b0010: shifted_data = {data_in[13:0], 2'b00};
      4'b0011: shifted_data = {data_in[12:0], 3'b000};
      4'b0100: shifted_data = {data_in[11:0], 4'b0000};
      4'b0101: shifted_data = {data_in[10:0], 5'b00000};
      4'b0110: shifted_data = {data_in[9:0], 6'b000000};
      4'b0111: shifted_data = {data_in[8:0], 7'b0000000};
      4'b1000: shifted_data = {data_in[7:0], 8'b00000000};
      4'b1001: shifted_data = {data_in[6:0], 9'b000000000};
      4'b1010: shifted_data = {data_in[5:0], 10'b0000000000};
      4'b1011: shifted_data = {data_in[4:0], 11'b00000000000};
      4'b1100: shifted_data = {data_in[3:0], 12'b000000000000};
      4'b1101: shifted_data = {data_in[2:0], 13'b0000000000000};
      4'b1110: shifted_data = {data_in[1:0], 14'b00000000000000};
      4'b1111: shifted_data = 15'b0;
      default: shifted_data = 16'b0;
    endcase
  end

  assign data_out = shifted_data;

endmodule
module barrel_shifter (
  input clk,
  input reset,
  input [7:0] data_in,
  input [2:0] shift_amount,
  input shift_direction, // 0: right shift, 1: left shift
  output [7:0] data_out
);

  reg [7:0] temp_data;

  always @ (posedge clk or posedge reset) begin
    if (reset) begin
      temp_data <= 8'h00;
    end else begin
      if (shift_direction == 1) begin // left shift
        temp_data[7:shift_amount] <= data_in[7-shift_amount:0];
        temp_data[shift_amount-1:0] <= 8'h00;
      end else begin // right shift
        temp_data[0:7-shift_amount] <= data_in[shift_amount-1:0];
        temp_data[7-shift_amount:7] <= 8'h00;
      end
    end
  end

  assign data_out = temp_data;

endmodule

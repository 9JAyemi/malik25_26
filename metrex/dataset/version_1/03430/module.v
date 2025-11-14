module crc(
  input [15:0] data_in,
  input crc_en,
  output reg [15:0] crc_out,
  input rst,
  input clk
);

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      crc_out <= 16'h0000;
    end else if (crc_en) begin
      crc_out <= data_in + 16'hA001;
    end
  end

endmodule

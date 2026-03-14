
module decoder_2to4 (
  input wire [1:0] in_data,
  output reg [3:0] out_data
);

always @(in_data) begin
  case (in_data)
    2'b00: out_data <= 4'b0001;
    2'b01: out_data <= 4'b0010;
    2'b10: out_data <= 4'b0100;
    2'b11: out_data <= 4'b1000;
    default: out_data <= 4'b0000;
  endcase
end

endmodule
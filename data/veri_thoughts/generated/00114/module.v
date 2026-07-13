
module data_parser(
  input [3:0] data_in,
  output reg [1:0] data_out_1,
  output reg [1:0] data_out_2,
  output reg parity
);

  always @(*) begin
    data_out_1 = data_in[1:0];
    data_out_2 = data_in[3:2];
    parity = ^data_in;
  end

endmodule
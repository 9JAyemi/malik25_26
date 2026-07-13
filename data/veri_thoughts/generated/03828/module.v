module gray_to_binary_decoder #(
  parameter width=32
)(
  input [width-1:0] gin,
  output [width-1:0] bout
);
  reg [width-1:0] breg;
  integer i;

  assign bout = breg;

  always @ (gin) begin
    breg[width-1] = gin[width-1];
    for (i = width-2; i >= 0; i = i - 1)
      breg[i] = gin[i] ^ breg[i+1];
  end
endmodule
module Multiplexer4 #(parameter width = 3)(
  input [width-1:0] i_data0,
  input [width-1:0] i_data1,
  input [width-1:0] i_data2,
  input [width-1:0] i_data3,
  input             i_select0,
  input             i_select1,
  input             i_select2,
  input             i_select3,
  output reg [width-1:0] o_data,
  output reg            o_error
);

  always @(*) begin
    case ({i_select3, i_select2, i_select1, i_select0})
      4'b0000: o_data = i_data0;
      4'b0001: o_data = i_data1;
      4'b0010: o_data = i_data2;
      4'b0011: o_data = i_data3;
      default: begin
        o_data = 0;
        o_error = 1;
      end
    endcase
  end
endmodule
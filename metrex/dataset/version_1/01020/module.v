
module mux5 #(parameter WIREWIDTH = 1) (input wire [2:0] s,
					input wire [WIREWIDTH:0] d0, d1, d2,d3, d4,
					output reg [WIREWIDTH:0] o);

   always @* begin
      case(s)
	0: o = d0;
	1: o = d1;
        2: o = d2;
        3: o = d3;
        default: o = d4;
      endcase
   end

endmodule
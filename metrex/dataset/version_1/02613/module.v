
module mux8
  #(parameter WIDTH=32, parameter DISABLED=0)
    (input en,
     input [2:0] sel,
     input [WIDTH-1:0] i0,
     input [WIDTH-1:0] i1,
     input [WIDTH-1:0] i2,
     input [WIDTH-1:0] i3,
     input [WIDTH-1:0] i4,
     input [WIDTH-1:0] i5,
     input [WIDTH-1:0] i6,
     input [WIDTH-1:0] i7,
     output [WIDTH-1:0] o);

   reg [WIDTH-1:0] _o;

   always @(*) begin
      case(sel)
         3'b000: _o = i0;
         3'b001: _o = i1;
         3'b010: _o = i2;
         3'b011: _o = i3;
         3'b100: _o = i4;
         3'b101: _o = i5;
         3'b110: _o = i6;
         3'b111: _o = i7;
         default: _o = DISABLED;
      endcase
   end

   assign o = en ? _o : DISABLED;

endmodule
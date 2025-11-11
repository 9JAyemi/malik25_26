module bar #(parameter OP_ADD = 2'b00) (
   input [3:0] a,
   input [3:0] b,
   input [1:0] sel,
   output reg [3:0] result
);
   
   always @(*) begin
      case(sel)
         2'b00: result = a + b;
         2'b01: result = a + ~b + 1;
         2'b10: result = a & b;
         2'b11: result = a | b;
         default: result = 4'b0;
      endcase
   end
   
   assign sel[1:0] = OP_ADD; // set sel value for addition operation
   
endmodule
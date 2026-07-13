
module main (val1, val2, result);

input [2:0] val1, val2;
output [2:0] result ;

assign result = (val1 == val2) ? val1 << 1 : 
               (val1 == 3'b000) ? 0 : 
               (val1 == 3'b001) ? 1 : 
               (val1 == 3'b010) ? 2 : 
               (val1 == 3'b011) ? 4 : 4;

endmodule
module shift_right(x,clk, rst,ld, shift, out);

 input clk;
 input rst;
 input ld;
 input shift;
 input [63:0] x;
 output reg  out;
 reg [63:0] shiftreg;
 

  always @(posedge clk or posedge rst) begin
       if (rst) begin
           shiftreg <= 0;
           out <= 1'b0;
       end
       else if (ld) begin
              shiftreg <= x;
              out <= 1'b0;
       end
       else if(shift) begin
            out <= shiftreg[0];
            shiftreg <= {1'b0,shiftreg[63:1]};  ;
       end
 end

endmodule

module calculator(
   input [7:0] a,
   input [7:0] b,
   input [1:0] op,
   input start,
   output reg done,
   output reg [7:0] result
   );

   reg [15:0] temp;
   reg [7:0] i;
   
   always@(posedge start)
   begin
      case(op)
         2'b00:result <= a + b;
         2'b01:result <= a - b;
         2'b10:result <= a * b;
         2'b11:begin
                  if(b == 0) begin
                     done <= 1;
                     result <= 8'hFF; // division by zero
                  end
                  else begin
                     temp <= a;
                     result <= 0;
                     for (i = 0; i < 8; i = i + 1) begin
                        if (temp >= b) begin
                           temp <= temp - b;
                           result[i] <= 1;
                        end
                        temp <= {temp[6:0], 1'b0};
                     end
                     done <= 1;
                  end
               end
         default:begin
                     done <= 1;
                     result <= 8'hFF; // invalid operation
                  end
      endcase
      done <= 0;
   end
   
endmodule
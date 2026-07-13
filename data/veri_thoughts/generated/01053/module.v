
module motor_controller(
   input clk,
   input rst,
   input [7:0] speed,
   output reg [7:0] motor_speed
);

   always @(posedge clk or posedge rst) begin
      if (rst) begin
         motor_speed <= 0;
      end else begin
         motor_speed <= speed;
      end
   end
endmodule
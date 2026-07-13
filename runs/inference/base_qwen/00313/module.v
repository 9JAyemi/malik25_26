module threshold_module(input [3:0] input_value, output reg [1:0] output_value);
   parameter THRESHOLD = 10;
   
   always @(*) begin
      if (input_value <= 5) begin
         output_value = 2'b00;
      end else if (input_value >= THRESHOLD) begin
         output_value = 2'b10;
      end else begin
         output_value = 2'b01;
      end
   end
endmodule
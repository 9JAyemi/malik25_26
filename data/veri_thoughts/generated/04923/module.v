module adder4(input [3:0] a, input [3:0] b, output reg [3:0] sum);
    wire [4:0] temp_sum;
    
    assign temp_sum = a + b;
    
    always @(*) begin
        if (temp_sum > 15) begin
            sum <= temp_sum - 16;
        end
        else begin
            sum <= temp_sum;
        end
    end
endmodule
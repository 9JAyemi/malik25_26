module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input C_in,
    input clk,
    output reg [3:0] S,
    output reg C_out
);

    wire [4:0] sum;
    wire carry; 
    
    assign sum = A + B + C_in;
    assign carry = sum[4];
    
    always @(posedge clk) begin
        S <= sum;
        C_out <= carry;
    end
    
endmodule
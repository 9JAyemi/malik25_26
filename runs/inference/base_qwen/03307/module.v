
module adder(input [7:0] A, input [7:0] B, output [7:0] S, output C_out);

    wire [8:0] sum;
    
    assign sum = A + B;
    
    assign S = sum[7:0];
    
    assign C_out = sum[8];

endmodule
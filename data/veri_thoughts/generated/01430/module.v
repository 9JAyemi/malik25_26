module eight_bit_adder (
    input [7:0] A,
    input [7:0] B,
    input Cin,
    output [7:0] S,
    output Cout
);

    wire [8:0] temp_sum;
    
    assign temp_sum = {1'b0, A} + {1'b0, B} + {1'b0, Cin};
    
    assign S = temp_sum[7:0];
    assign Cout = temp_sum[8];
    
endmodule
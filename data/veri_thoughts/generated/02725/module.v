
module binary_addition(
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

    wire [8:0] temp_sum;
    
    assign temp_sum = a + b;
    assign sum = temp_sum[7:0];
    
endmodule
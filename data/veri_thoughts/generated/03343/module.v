module adder_4bit (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [4:0] temp_sum;
    
    assign temp_sum = a + b + cin;
    assign sum = temp_sum[3:0];
    assign cout = temp_sum[4];
    
endmodule
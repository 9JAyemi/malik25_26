module top_module ( 
    input clk, 
    input [3:0] A,
    input [3:0] B,
    input select,
    output [3:0] sum );

    wire [3:0] sum1, sum2;
    wire enable1, enable2;

    // Adder 1
    adder_4bit adder1(.A(A), .B(B), .sum(sum1));

    // Adder 2
    adder_4bit adder2(.A(A), .B(B), .sum(sum2));

    // Control Logic
    assign enable1 = (select == 0);
    assign enable2 = (select == 1);

    // Output
    assign sum = enable1 ? sum1 : sum2;

endmodule

// 4-bit Adder module
module adder_4bit ( 
    input [3:0] A,
    input [3:0] B,
    output [3:0] sum );

    assign sum = A + B;

endmodule
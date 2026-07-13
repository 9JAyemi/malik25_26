
module top_module ( 
    input clk, 
    input reset, // Synchronous active-high reset 
    input [3:0] a, // 4-bit input for the adder module 
    input [3:0] b, // 4-bit input for the adder module 
    input [1:0] sel, // Select input to choose between adder and multiplexer 
    output [3:0] q // 4-bit output from the active module 
); 




// Control logic to select between adder and multiplexer
assign q = (sel == 2'b00) ? {1'b0, a} : {1'b1, b};

endmodule

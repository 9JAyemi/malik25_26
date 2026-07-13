
module binary_add_sub (
    input clk,
    input reset,      // Synchronous active-high reset
    input [31:0] a,   // 32-bit input a
    input [31:0] b,   // 32-bit input b
    input sub,        // Select input for addition or subtraction
    input enable,     // Enable input for the storage module
    output [31:0] sum // 32-bit output for the selected operation
);

    // 8-bit binary number storage module
    reg [7:0] stored_num = 8'h34;
    
    // Adder-subtractor module for 32-bit binary numbers
    wire [31:0] result;
    wire [31:0] inverted_b = sub ? ~b + 1 : b;
    assign result = a + inverted_b;
    
    // Carry-lookahead adder architecture
    wire [31:0] g, p, c;
    assign g = result & {32{1'b1}};
    assign p = a ^ inverted_b;
    assign c[0] = sub;
    generate
        genvar i;
        for (i = 1; i < 32; i = i + 1) begin : carry_gen
            assign c[i] = g[i-1] | (p[i-1] & c[i-1]);
        end
    endgenerate
    
    // Output
    
    assign sum = result; // Fixed the RTL code by assigning the result to the output sum 
    
    always @(posedge clk) begin
        if (reset) begin
            stored_num <= 8'h34;
            // Remove the assignment to sum here
        end else if (enable) begin
            stored_num <= result[7:0];
        end else begin
            // Remove the assignment to sum here
        end
    end

endmodule
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [31:0] a,   // 32-bit input a
    input [31:0] b,   // 32-bit input b
    input sub,        // Select input for addition or subtraction
    input enable,     // Enable input for the storage module
    output [31:0] sum // 32-bit output for the selected operation
);
    
    binary_add_sub add_sub (
        .clk(clk),
        .reset(reset),
        .a(a),
        .b(b),
        .sub(sub),
        .enable(enable),
        .sum(sum)
    );

endmodule
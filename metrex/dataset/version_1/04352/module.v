
module top_module ( 
    input clk, // Clock signal
    input reset, // Active high synchronous reset
    input [7:0] a, // 8-bit input a 
    input [7:0] b, // 8-bit input b
    output reg [15:0] sum // 16-bit output sum
);

    reg [7:0] fa_out1; // Output of first full adder
    reg [7:0] carry; // Carry output from full adders

    full_adder fa1(.a(a[0]), .b(b[0]), .cin(1'b0), .sum(fa_out1[0]), .cout(carry[0])); // First full adder
    full_adder fa2(.a(a[1]), .b(b[1]), .cin(carry[0]), .sum(fa_out1[1]), .cout(carry[1])); // Second full adder
    full_adder fa3(.a(a[2]), .b(b[2]), .cin(carry[1]), .sum(fa_out1[2]), .cout(carry[2])); // Third full adder
    full_adder fa4(.a(a[3]), .b(b[3]), .cin(carry[2]), .sum(fa_out1[3]), .cout(carry[3])); // Fourth full adder
    full_adder fa5(.a(a[4]), .b(b[4]), .cin(carry[3]), .sum(fa_out1[4]), .cout(carry[4])); // Fifth full adder
    full_adder fa6(.a(a[5]), .b(b[5]), .cin(carry[4]), .sum(fa_out1[5]), .cout(carry[5])); // Sixth full adder
    full_adder fa7(.a(a[6]), .b(b[6]), .cin(carry[5]), .sum(fa_out1[6]), .cout(carry[6])); // Seventh full adder
    full_adder fa8(.a(a[7]), .b(b[7]), .cin(carry[6]), .sum(fa_out1[7]), .cout(carry[7])); // Eighth full adder

    always @(posedge clk) begin
        if(reset) begin
            sum <= 16'b0; // Reset sum to 0
        end else begin
            sum <= {carry[7], fa_out1}; // Concatenate carry and output of first full adder
        end
    end

endmodule
module full_adder (
    input a,
    input b,
    input cin,
    output reg sum,
    output reg cout
);

    always @(*) begin
        sum = a ^ b ^ cin; // Calculate sum
        cout = (a & b) | (a & cin) | (b & cin); // Calculate carry
    end

endmodule
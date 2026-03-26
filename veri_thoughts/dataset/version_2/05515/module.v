module top_module (
    input [3:0] A, B, // Two 4-bit inputs
    input carry_in, // Carry input for the ripple carry adder
    output [3:0] sum, // 4-bit output from the ripple carry adder
    output carry_out, // Carry output from the ripple carry adder
    output EQ, GT, LT // Comparison outputs from the functional module
);

    // Ripple carry adder
    wire [3:0] adder_out;
    wire carry_out_internal;
    ripple_carry_adder adder(.A(A), .B(B), .carry_in(carry_in), .sum(adder_out), .carry_out(carry_out_internal));
    
    // Output sum and carry_out from the adder
    assign sum = adder_out;
    assign carry_out = carry_out_internal;
    
    // Functional module for comparison
    assign EQ = (A == B);
    assign GT = (A > B);
    assign LT = (A < B);
    
endmodule

// Ripple carry adder module
module ripple_carry_adder (
    input [3:0] A, B, // Two 4-bit inputs
    input carry_in, // Carry input
    output [3:0] sum, // 4-bit output from the adder
    output carry_out // Carry output from the adder
);

    wire [3:0] sum_internal;
    wire [3:0] carry_out_internal;
    
    // Full adder for the least significant bit
    full_adder adder0(.A(A[0]), .B(B[0]), .carry_in(carry_in), .sum(sum_internal[0]), .carry_out(carry_out_internal[0]));
    
    // Ripple carry adder for the remaining bits
    genvar i;
    generate
        for (i = 1; i < 4; i = i + 1) begin : adder_loop
            full_adder adder(.A(A[i]), .B(B[i]), .carry_in(carry_out_internal[i-1]), .sum(sum_internal[i]), .carry_out(carry_out_internal[i]));
        end
    endgenerate
    
    // Output sum and carry_out from the adder
    assign sum = sum_internal;
    assign carry_out = carry_out_internal[3];
    
endmodule

// Full adder module
module full_adder (
    input A, B, carry_in, // Three inputs
    output sum, carry_out // Two outputs
);

    assign sum = A ^ B ^ carry_in;
    assign carry_out = (A & B) | (carry_in & (A ^ B));
    
endmodule
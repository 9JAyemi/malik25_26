module adder_4bit (
    input [3:0] A, B,
    output [3:0] S,
    output C_out
);

    wire [3:0] sum; 
    wire [3:0] carry; 
    
    // First Full Adder
    full_adder FA1(A[0], B[0], 1'b0, sum[0], carry[0]);
    
    // Second Full Adder
    full_adder FA2(A[1], B[1], carry[0], sum[1], carry[1]);
    
    // Third Full Adder
    full_adder FA3(A[2], B[2], carry[1], sum[2], carry[2]);
    
    // Fourth Full Adder
    full_adder FA4(A[3], B[3], carry[2], sum[3], C_out);
    
    assign S = sum;
    
endmodule

module full_adder (
    input A, B, Cin,
    output S, Cout
);

    assign {Cout, S} = A + B + Cin;
    
endmodule
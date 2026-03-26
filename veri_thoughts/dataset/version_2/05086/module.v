module binary_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] adder_output;
    wire [3:0] carry_out;
    
    // 4-bit binary adder with carry-in and carry-out functionality
    // This adder is implemented using four full adders
    full_adder FA0(.A(A[0]), .B(B[0]), .Cin(Cin), .S(adder_output[0]), .Cout(carry_out[0]));
    full_adder FA1(.A(A[1]), .B(B[1]), .Cin(carry_out[0]), .S(adder_output[1]), .Cout(carry_out[1]));
    full_adder FA2(.A(A[2]), .B(B[2]), .Cin(carry_out[1]), .S(adder_output[2]), .Cout(carry_out[2]));
    full_adder FA3(.A(A[3]), .B(B[3]), .Cin(carry_out[2]), .S(adder_output[3]), .Cout(Cout));
    
    assign S = adder_output;
    
endmodule

module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    // XOR gate for sum output
    assign S = A ^ B ^ Cin;
    
    // AND gate for carry output
    assign Cout = (A & B) | (A & Cin) | (B & Cin);
    
endmodule
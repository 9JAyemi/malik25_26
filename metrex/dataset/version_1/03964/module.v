module ripple_carry_adder (A, B, Cin, Sum, Cout);

    parameter WIDTH = 4;
    
    input [WIDTH-1:0] A, B;
    input Cin;
    output [WIDTH-1:0] Sum;
    output Cout;
    
    wire [WIDTH:0] C;
    assign C[0] = Cin;
    
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_full_adder
            full_adder fa(
                .A(A[i]),
                .B(B[i]),
                .Cin(C[i]),
                .Sum(Sum[i]),
                .Cout(C[i+1])
            );
        end
    endgenerate
    
    assign Cout = C[WIDTH];
    
endmodule

module full_adder (A, B, Cin, Sum, Cout);

    input A, B, Cin;
    output Sum, Cout;
    
    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));
    
endmodule
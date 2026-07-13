module ripple_carry_adder #(parameter WIDTH = 4) (input [WIDTH-1:0] A, input [WIDTH-1:0] B, input CI, output [WIDTH-1:0] S, output CO);
    
    wire [WIDTH:0] C;
    assign C[0] = CI;
    
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin:adder
            full_adder FA(
                .A(A[i]),
                .B(B[i]),
                .CI(C[i]),
                .S(S[i]),
                .CO(C[i+1])
            );
        end
    endgenerate
    
    assign CO = C[WIDTH];
    
endmodule

module full_adder (input A, input B, input CI, output S, output CO);
    
    assign S = A ^ B ^ CI;
    assign CO = (A & B) | (CI & (A ^ B));
    
endmodule
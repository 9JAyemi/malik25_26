module ripple_adder #(parameter DW = 4)
    (
        input [DW-1:0] A,
        input [DW-1:0] B,
        input Cin,
        output [DW-1:0] S,
        output Cout
    );
    
    wire [DW:0] carry;
    
    assign carry[0] = Cin;
    
    genvar i;
    generate
        for (i = 0; i < DW; i = i + 1) begin
            full_adder #(DW) fa(A[i], B[i], carry[i], S[i], carry[i+1]);
        end
    endgenerate
    
    assign Cout = carry[DW];
    
endmodule

module full_adder #(parameter DW = 4)
    (
        input A,
        input B,
        input Cin,
        output S,
        output Cout
    );
    
    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));
    
endmodule
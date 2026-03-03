
module RippleCarryAdder(
    A,
    B,
    Cin,
    S,
    Cout
);

    input [3:0] A;
    input [3:0] B;
    input Cin;
    output [3:0] S;
    output Cout;
    
    wire [3:0] C;
    
    assign C = {1'b0, 1'b0, 1'b0, Cin};
    assign S = A ^ B ^ C;
    assign Cout = (A & B) | (C & (A ^ B));
    
endmodule
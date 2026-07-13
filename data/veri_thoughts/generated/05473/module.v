
module adder4bit (A, B, Cin, CK, S, Cout);
input [3:0] A;
input [3:0] B;
input Cin;
input CK;
output [3:0] S;
output Cout;

reg [3:0] S;
reg Cout;

always @(posedge CK) begin
    {Cout, S} <= A + B + Cin;
end

endmodule
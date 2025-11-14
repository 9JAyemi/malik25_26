module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output reg [3:0] S,
    output reg Cout
);

reg [4:0] Sum;

always @* begin
    Sum = {1'b0, A} + {1'b0, B} + Cin;
    S = Sum[3:0];
    Cout = Sum[4];
end

endmodule
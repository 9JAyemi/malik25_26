
module ripple_carry_adder (
    input clk,
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output reg [3:0] S,
    output reg V
);

    wire [3:0] C;
    wire [3:0] X;
    full_adder FA0(.a(A[0]), .b(B[0]), .c_in(Cin), .s(X[0]), .c(C[0]));
    full_adder FA1(.a(A[1]), .b(B[1]), .c_in(C[0]), .s(X[1]), .c(C[1]));
    full_adder FA2(.a(A[2]), .b(B[2]), .c_in(C[1]), .s(X[2]), .c(C[2]));
    full_adder FA3(.a(A[3]), .b(B[3]), .c_in(C[2]), .s(X[3]), .c(C[3]));

    always @(posedge clk) begin
        S <= X;
        V <= C[3];
    end

endmodule
module full_adder (
    input a,
    input b,
    input c_in,
    output s,
    output c
);

    assign s = a ^ b ^ c_in;
    assign c = (a & b) | (a & c_in) | (b & c_in);

endmodule
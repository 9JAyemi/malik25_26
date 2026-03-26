
module full_adder(a, b, cin, s, cout);
    input a, b, cin;
    output s, cout;

    wire w1, w2, w3;

    assign w1 = a ^ b;
    assign s = w1 ^ cin;
    assign w2 = a & b;
    assign w3 = cin & w1;
    assign cout = w2 | w3;
endmodule
module ripple_carry_adder(A, B, Cin, S, Cout);
    parameter WIDTH = 4;
    input [WIDTH-1:0] A, B;
    input Cin;
    output [WIDTH-1:0] S;
    output Cout;

    wire [WIDTH:0] carry;

    genvar i;
    generate
        for(i = 0; i < WIDTH; i = i + 1) begin : gen_full_adder
            full_adder fa(
                .a(A[i]),
                .b(B[i]),
                .cin(carry[i]),
                .s(S[i]),
                .cout(carry[i+1])
            );
        end
    endgenerate

    assign carry[0] = Cin;
    assign Cout = carry[WIDTH];
endmodule

module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    assign {Cout, Sum} = A + B + Cin;

endmodule

module decoder_4to16 (
    input [1:0] A,
    output reg [15:0] O
);

    always @(*) begin
        case (A)
            2'b00: O = 16'b0000000000000001;
            2'b01: O = 16'b0000000000000010;
            2'b10: O = 16'b0000000000000100;
            2'b11: O = 16'b0000000000001000;
        endcase
    end

endmodule

module ripple_decoder_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout,
    output [15:0] O
);

    wire [3:0] adder_sum;
    wire adder_cout;
    wire [1:0] decoder_input;

    ripple_carry_adder adder(  // Assuming ripple_carry_adder is a separate module
        .A(A),
        .B(B),
        .Cin(Cin),
        .Sum(adder_sum),
        .Cout(adder_cout)
    );

    assign decoder_input = adder_sum[3:2];

    decoder_4to16 decoder(   // Assuming decoder_4to16 is a separate module
        .A(decoder_input),
        .O(O)
    );

    assign Sum = adder_sum;
    assign Cout = adder_cout;

endmodule

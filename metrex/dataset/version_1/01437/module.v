
module signed_mult_shift(
    input signed [3:0] A,
    input signed [3:0] B,
    input [3:0] shift,
    input dir,
    output reg signed [15:0] out
);

    wire signed [7:0] mult_result;
    wire [3:0] shift_amt;

    // Signed multiplication module
    signed_mult mult(
        .A(A),
        .B(B),
        .out(mult_result)
    );

    // Determine shift amount based on direction input
    assign shift_amt = (dir == 1'b1) ? shift : -shift;

    // Instantiate the barrel shifter module
    barrel_shifter shift_reg(
        .in(mult_result),
        .shift_amt(shift_amt),
        .out(out)
    );

endmodule
module signed_mult(
    input signed [3:0] A,
    input signed [3:0] B,
    output reg signed [7:0] out
);

    wire [7:0] temp;
    assign temp = A * B;
    always @(*) begin
        out = temp;
    end

endmodule
module barrel_shifter(
    input [7:0] in,
    input [3:0] shift_amt,
    output reg [15:0] out
);

    always @(*) begin
        out = in << shift_amt;
    end

endmodule
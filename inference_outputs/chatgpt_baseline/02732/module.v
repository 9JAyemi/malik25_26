
module top_module (
    input [15:0] A,
    input [15:0] B,
    input [3:0] shift_amount,
    output [15:0] result
);

    wire A_greater_B;
    magnitude_comparator mag_comp(A, B, A_greater_B);
    barrel_shifter barrel_shift(A, B, shift_amount, A_greater_B, result);

endmodule

module magnitude_comparator (
    input [15:0] A,
    input [15:0] B,
    output reg A_greater_B
);

    always @* begin
        if (A > B)
            A_greater_B = 1;
        else
            A_greater_B = 0;
    end

endmodule

module barrel_shifter (
    input [15:0] A,
    input [15:0] B,
    input [3:0] shift_amount,
    input A_greater_B,
    output reg [15:0] result
);

    always @* begin
        if (A_greater_B)
            result = A << shift_amount;
        else if (A < B)
            result = B >> shift_amount;
        else
            result = A;
    end

endmodule

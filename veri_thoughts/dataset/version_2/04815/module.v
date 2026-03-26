
module ripple_shift_adder (
    input [3:0] A,
    input [3:0] B,
    input carry_in,
    input select,
    output [3:0] out,
    output carry_out
);

    wire [3:0] adder_out;
    wire [3:0] shift_out;

    ripple_carry_adder #(4) adder(.A(A), .B(B), .carry_in(carry_in), .sum(adder_out), .carry_out(carry_out));
    barrel_shifter shifter(.in(A), .shift(B), .select(select), .out(shift_out));

    assign out = select ? shift_out : adder_out;

endmodule
module barrel_shifter (
    input [3:0] in,
    input [3:0] shift,
    input select,
    output [3:0] out
);

    wire [3:0] out_temp;

    assign out_temp = in << shift;
    assign out = select ? out_temp : in;

endmodule
module ripple_carry_adder #(parameter N = 4) (
    input [N-1:0] A,
    input [N-1:0] B,
    input carry_in,
    output [N-1:0] sum,
    output carry_out
);

    wire [N:0] carry;

    assign carry[0] = carry_in;

    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : adder_cells
            full_adder adder_cell(.A(A[i]), .B(B[i]), .carry_in(carry[i]), .sum(sum[i]), .carry_out(carry[i+1]));
        end
    endgenerate

    assign carry_out = carry[N];

endmodule
module full_adder (
    input A,
    input B,
    input carry_in,
    output sum,
    output carry_out
);

    assign sum = A ^ B ^ carry_in;
    assign carry_out = (A & B) | (A & carry_in) | (B & carry_in);

endmodule
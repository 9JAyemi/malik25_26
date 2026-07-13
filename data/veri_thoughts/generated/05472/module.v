
module add_sub_shift (
    input [3:0] in0,
    input [3:0] in1,
    input SUB,
    input [1:0] SHIFT,
    input select,
    output reg [3:0] Y
);

    wire [3:0] add_sub_out;
    wire [3:0] shift_out;

    add_sub add_sub_inst (
        .in0(in0),
        .in1(in1),
        .SUB(SUB),
        .Y(add_sub_out)
    );

    barrel_shifter barrel_shifter_inst (
        .in(add_sub_out),
        .SHIFT(SHIFT),
        .Y(shift_out)
    );

    always @(*) begin
        if (select) begin
            Y <= shift_out;
        end else begin
            Y <= add_sub_out;
        end
    end

endmodule

module add_sub (
    input [3:0] in0,
    input [3:0] in1,
    input SUB,
    output reg [3:0] Y
);

    always @(*) begin
        if (SUB) begin
            Y <= in0 - in1;
        end else begin
            Y <= in0 + in1;
        end
    end

endmodule

module barrel_shifter (
    input [3:0] in,
    input [1:0] SHIFT,
    output [3:0] Y
);

    assign Y = (SHIFT[1]) ? (in >> SHIFT) : (in << SHIFT);

endmodule

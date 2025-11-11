module add_sub_and (
    input wire [7:0] in1,
    input wire [7:0] in2,
    input wire ctrl,
    output wire [7:0] out,
    output wire [7:0] out_and
);

    wire [7:0] add_in;
    wire [7:0] sub_in;
    wire [7:0] add_out;
    wire [7:0] and_out;

    // 2-to-1 multiplexer to select input based on control input
    mux2to1 mux (
        .in0(in1),
        .in1(in2),
        .sel(ctrl),
        .out(add_in)
    );

    assign sub_in = in2; // Assign sub_in to in2 for subtraction

    // 8-bit adder to perform addition or subtraction
    adder8 adder (
        .in1(add_in),
        .in2(sub_in),
        .sub(ctrl),
        .out(add_out)
    );

    // Bitwise AND module to perform AND operation on inputs
    and8 and_gate (
        .in1(in1),
        .in2(in2),
        .out(and_out)
    );

    assign out = add_out;
    assign out_and = and_out;

endmodule

module mux2to1 (
    input [7:0] in0,
    input [7:0] in1,
    input sel,
    output reg [7:0] out
);
    always @(*) begin
        if (sel == 1'b0)
            out = in0;
        else
            out = in1;
    end
endmodule

module adder8 (
    input [7:0] in1,
    input [7:0] in2,
    input sub,
    output reg [7:0] out
);
    always @(*) begin
        if (sub)
            out = in1 - in2;
        else
            out = in1 + in2;
    end
endmodule

module and8 (
    input [7:0] in1,
    input [7:0] in2,
    output reg [7:0] out
);
    always @* begin
        out = in1 & in2;
    end
endmodule
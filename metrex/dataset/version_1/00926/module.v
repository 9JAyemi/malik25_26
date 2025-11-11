
module and_display_module(
    input [3:0] a,
    input [3:0] b,
    input clk,
    output [6:0] seg_out,
    output [7:0] out_not
);

    // bitwise AND module
    wire [3:0] and_out;
    and_module and_inst(
        .a(a),
        .b(b),
        .out(and_out)
    );

    // logical AND module
    wire [3:0] logical_and_out;
    logical_and_module logical_and_inst(
        .a(a),
        .b(b),
        .out(logical_and_out)
    );

    // NOT module for input a
    wire [3:0] not_a_out;
    not_module not_a_inst(
        .in(a),
        .out(not_a_out)
    );

    // NOT module for input b
    wire [3:0] not_b_out;
    not_module not_b_inst(
        .in(b),
        .out(not_b_out)
    );

    // combine NOT outputs into single output
    assign out_not = {not_a_out, not_b_out};

    // final output module
    seven_segment_module seven_seg_inst(
        .in(and_out & logical_and_out),
        .out(seg_out)
    );

endmodule

module and_module(
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] out
);
    always @* begin
        out = a & b;
    end
endmodule

module logical_and_module(
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] out
);
    always @* begin
        out = (a != 0) && (b != 0);
    end
endmodule

module not_module(
    input [3:0] in,
    output reg [3:0] out
);
    always @* begin
        out = ~in;
    end
endmodule

module seven_segment_module(
    input [3:0] in,
    output reg [6:0] out
);
    always @* begin
        case (in)
            4'b0000: out = 7'b1000000; // 0
            4'b0001: out = 7'b1111001; // 1
            4'b0010: out = 7'b0100100; // 2
            4'b0011: out = 7'b0110000; // 3
            4'b0100: out = 7'b0011001; // 4
            4'b0101: out = 7'b0010010; // 5
            4'b0110: out = 7'b0000010; // 6
            4'b0111: out = 7'b1111000; // 7
            4'b1000: out = 7'b0000000; // 8
            4'b1001: out = 7'b0011000; // 9
            default: out = 7'b1111111; // off
        endcase
    end
endmodule

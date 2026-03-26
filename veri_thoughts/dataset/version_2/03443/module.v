
module multiplexer (
    input a,
    input b,
    input c,
    input [1:0] select,
    output reg [3:0] out
);

always @* begin
    case (select)
        2'b00: out = {a, 2'b00};
        2'b01: out = {2'b00, b};
        2'b10: out = {2'b00, c};
        2'b11: out = {2'b11, 2'b00};
    endcase;
end

endmodule
module or_gate (
    input a,
    input b,
    input c,
    output out
);

assign out = a | b | c;

endmodule
module final_module (
    input [3:0] mux_out,
    input or_out,
    input select,
    output final_output
);

assign final_output = select ? mux_out : or_out;

endmodule
module top_module (
    input a,
    input b,
    input c,
    input [1:0] select,
    output out_assign,
    output out_alwaysblock,
    output final_output
);

wire [3:0] mux_out;
wire or_out;

multiplexer mux_inst (
    .a(a),
    .b(b),
    .c(c),
    .select(select),
    .out(mux_out)
);

or_gate or_inst (
    .a(a),
    .b(b),
    .c(c),
    .out(or_out)
);

final_module final_inst (
    .mux_out(mux_out),
    .or_out(or_out),
    .select(select[0]),
    .final_output(final_output)
);

assign out_assign = mux_out; // Assign the output of the multiplexer to out_assign
assign out_alwaysblock = or_out; // Assign the output of the or_gate to out_alwaysblock

endmodule

module or_gate(
    input a,
    input b,
    output reg out
);

always @(*) begin
    out = a | b;
end

endmodule
module final_output(
    input a,
    input b,
    output reg [1:0] out
);

always @(*) begin
    out[0] = a | b;
    out[1] = a | b;
end

endmodule
module top_module(
    input a,
    input b,
    output out
);

wire [1:0] internal_out;
or_gate or_inst(
    .a(a),
    .b(b),
    .out(internal_out[0])
);

final_output final_inst(
    .a(a),
    .b(b),
    .out({out, internal_out[0]})
);

endmodule
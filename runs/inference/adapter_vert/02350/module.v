module top_module (
    input a,
    input b,
    input c,
    input reset,
    output out
);

wire xor_out;
wire or_out;

xor_gate xor_inst (
    .a(a),
    .b(b),
    .out(xor_out)
);

or_gate_assign or_inst (
    .a(xor_out),
    .b(c),
    .c(reset),
    .out(or_out)
);

output_module output_inst (
    .xor_out(xor_out),
    .or_out(or_out),
    .out(out)
);

endmodule

module xor_gate (
    input a,
    input b,
    output out
);

assign out = a ^ b;

endmodule

module or_gate_assign (
    input a,
    input b,
    input c,
    output out
);

assign out = a | b | c;

endmodule

module or_gate_alwaysblock (
    input a,
    input b,
    input c,
    input reset,
    output reg out
);

always @ (a or b or c or reset) begin
    if (reset) begin
        out <= 1'b0;
    end else begin
        out <= a | b | c;
    end
end

endmodule

module output_module (
    input xor_out,
    input or_out,
    output out
);

assign out = xor_out & or_out;

endmodule
module xor_gate(
    input a,
    input b,
    output out
);

wire w1, w2, w3;

and_gate and1(.a(a), .b(~b), .out(w1));
and_gate and2(.a(~a), .b(b), .out(w2));
or_gate or1(.a(w1), .b(w2), .out(w3));
not_gate not1(.a(w3), .out(out));

endmodule

module and_gate(
    input a,
    input b,
    output out
);

assign out = a & b;

endmodule

module or_gate(
    input a,
    input b,
    output out
);

assign out = a | b;

endmodule

module not_gate(
    input a,
    output out
);

assign out = ~a;

endmodule

module top_module(
    input clk,
    input a,
    input b,
    output out_always_ff
);

reg a_ff, b_ff;

always @(posedge clk) begin
    a_ff <= a;
    b_ff <= b;
end

xor_gate xor1(.a(a_ff), .b(b_ff), .out(out_always_ff));

endmodule
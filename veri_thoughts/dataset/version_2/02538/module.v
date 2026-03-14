module and_or_gate (
    input a,
    input b,
    input c,
    output y
);

    wire and_out;
    wire or_out;

    and_gate and1 (.a(a), .b(b), .y(and_out));
    or_gate or1 (.a(a), .b(b), .y(or_out));
    assign y = and_out & or_out;

endmodule

module and_gate (
    input a,
    input b,
    output y
);

    assign y = a & b;

endmodule

module or_gate (
    input a,
    input b,
    output y
);

    assign y = a | b;

endmodule
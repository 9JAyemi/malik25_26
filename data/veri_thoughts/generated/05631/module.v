module top_module (
    input [2:0] in,
    input select,
    output and_result,
    output or_result,
    output xor_result
);

    wire and_out, or_out;

    and_gate and_inst (
        .in(in),
        .and_result(and_out)
    );

    or_gate or_inst (
        .in(in),
        .or_result(or_out)
    );

    assign and_result = select ? 0 : and_out;
    assign or_result = select ? or_out : 0;
    assign xor_result = and_out ^ or_out;

endmodule

module and_gate (
    input [2:0] in,
    output and_result
);

    assign and_result = in[0] & in[1] & in[2];

endmodule

module or_gate (
    input [2:0] in,
    output or_result
);

    assign or_result = in[0] | in[1] | in[2];

endmodule
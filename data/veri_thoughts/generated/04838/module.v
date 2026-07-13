
module top_module (
    input a,
    input b,
    input select,
    output out
);

    wire and_out;
    wire xor_out;

    and_gate and_inst (
        .a(a),
        .b(b),
        .out(and_out)
    );

    xor_gate xor_inst (
        .a(a),
        .b(b),
        .out(xor_out)
    );

    functional_module func_inst (
        .and_out(and_out),
        .xor_out(xor_out),
        .select(select),
        .final_out(out)
    );

endmodule

module and_gate (
    input a,
    input b,
    output reg out
);

    always @(a or b) begin
        out = a & b;
    end

endmodule

module xor_gate (
    input a,
    input b,
    output reg out
);

    always @(a or b) begin
        out = a ^ b;
    end

endmodule

module functional_module (
    input and_out,
    input xor_out,
    input select,
    output final_out
);

    assign final_out = (select == 1'b0) ? and_out : xor_out;

endmodule

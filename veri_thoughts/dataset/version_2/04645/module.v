
module top_module (
    input [1:0] a,
    input [49:0] in,
    output [5:0] out
);

    wire xor_out;
    wire [2:0] comb_out;

    xor_gate xor_inst (
        .a(a[0]),
        .b(a[1]),
        .out(xor_out)
    );

    comb_circuit_50_input comb_inst (
        .in(in),
        .out(comb_out)
    );

    assign out = {xor_out, comb_out, 2'b00};

endmodule

module xor_gate (
    input a,
    input b,
    output out
);

    assign out = (a ^ b);

endmodule

module comb_circuit_50_input (
    input [49:0] in,
    output [2:0] out
);

    assign out[0] = ~(&in);
    assign out[1] = ~(|in);
    assign out[2] = ~(^in);

endmodule


module top_module (
    input [15:0] D,
    input [15:0] V,
    output equal,
    output greater,
    output [3:0] Q_out
);

wire equal_comp, greater_comp;
wire [15:0] Q, R;

mag_comp mag_comp_inst (
    .A(D[3:0]),
    .B(V[3:0]),
    .equal(equal_comp),
    .greater(greater_comp)
);

div_16bit_unsigned div_inst (
    .D(D),
    .V(V),
    .Q(Q),
    .R(R)
);

functional_module func_mod_inst (
    .equal(equal_comp),
    .greater(greater_comp),
    .Q_in(Q),
    .Q_out(Q_out)
);

assign equal = equal_comp;
assign greater = greater_comp;

endmodule
module mag_comp (
    input [3:0] A,
    input [3:0] B,
    output equal,
    output greater
);

    assign equal = (A == B);
    assign greater = (A > B);

endmodule
module div_16bit_unsigned (
    input [15:0] D,
    input [15:0] V,
    output [15:0] Q,
    output [15:0] R
);

    assign Q = D / V;
    assign R = D % V;

endmodule
module functional_module (
    input equal,
    input greater,
    input [15:0] Q_in,
    output reg [3:0] Q_out
);

    always @(*) begin
        if (greater) begin
            Q_out = Q_in[15:12];
        end else begin
            Q_out = Q_in[3:0];
        end
    end
endmodule
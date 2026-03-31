
module splitter(
    input wire [15:0] in,
    output wire [7:0] out1,
    output wire [7:0] out2
);
    assign out1 = in[7:0];
    assign out2 = in[15:8];
endmodule
module and_gate(
    input wire a,
    input wire b,
    output wire out
);
    assign out = a & b;
endmodule
module top_module(
    input wire [15:0] in,
    output wire out
);
    wire [7:0] out1;
    wire [7:0] out2;

    splitter splitter_inst(.in(in), .out1(out1), .out2(out2));
    and_gate and_gate_inst(.a(out2[0]), .b(out1[0]), .out(out));
endmodule
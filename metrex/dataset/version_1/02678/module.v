module nand_gate_pipeline(
    input a,
    input b,
    output reg out
);

reg [1:0] stage1;
reg stage2;

always @(a, b) begin
    stage1[0] <= a & b;
    stage1[1] <= #1 ~stage1[0];
    stage2 <= #1 ~stage1[1];
    out <= #1 ~stage2;
end

endmodule

module decoder_2to4(
    input [1:0] in,
    output reg [3:0] out
);

wire nand1, nand2, nand3, nand4;

nand_gate_pipeline nand_gate1(.a(in[0]), .b(in[1]), .out(nand1));
nand_gate_pipeline nand_gate2(.a(~in[0]), .b(in[1]), .out(nand2));
nand_gate_pipeline nand_gate3(.a(in[0]), .b(~in[1]), .out(nand3));
nand_gate_pipeline nand_gate4(.a(~in[0]), .b(~in[1]), .out(nand4));

always @(in) begin
    out[0] <= #1 nand1;
    out[1] <= #1 nand2;
    out[2] <= #1 nand3;
    out[3] <= #1 nand4;
end

endmodule

module top_module(
    input a,
    input b,
    output reg [3:0] out
);

wire [1:0] in;
assign in = {a, b};

decoder_2to4 decoder(.in(in), .out(out));

endmodule
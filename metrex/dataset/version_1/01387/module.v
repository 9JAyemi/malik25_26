module top_module (
    input clk,
    input [255:0] in0,
    input [7:0] sel0,
    input [255:0] in1,
    input [7:0] sel1,
    input select,
    output [7:0] sum
);

reg [255:0] mux_in;
reg [7:0] mux_sel;
wire mux_out0, mux_out1;

always @(posedge clk) begin
    if (select) begin
        mux_in <= in1;
        mux_sel <= sel1;
    end else begin
        mux_in <= in0;
        mux_sel <= sel0;
    end
end

mux256to1 mux0 (.in(mux_in), .sel(mux_sel), .out(mux_out0));
mux256to1 mux1 (.in(in1), .sel(sel1), .out(mux_out1));

reg [3:0] adder_in0, adder_in1;
always @(posedge clk) begin
    adder_in0 <= {4{mux_out0}};
    adder_in1 <= {4{mux_out1}};
end

adder4bit adder (.a(adder_in0), .b(adder_in1), .sum(sum));

endmodule

module mux256to1 (
    input [255:0] in,
    input [7:0] sel,
    output out
);

assign out = in[sel];

endmodule

module adder4bit (
    input [3:0] a,
    input [3:0] b,
    output [7:0] sum
);

wire [4:0] tmp_sum;

assign tmp_sum = a + b;
assign sum = {tmp_sum[4], tmp_sum[3:0], 3'b0};

endmodule
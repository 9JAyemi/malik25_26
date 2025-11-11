module pipeline_splitter (
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    input wire clk
);

wire [15:0] stage1_out;
wire [7:0] stage2_out;

pipeline_stage1 stage1(.in(in), .clk(clk), .out(stage1_out));
pipeline_stage2 stage2(.in(stage1_out[7:0]), .clk(clk), .out(stage2_out));

assign out_hi = stage2_out;
assign out_lo = stage1_out[15:8];

endmodule

module pipeline_stage1 (
    input wire [15:0] in,
    input wire clk,
    output reg [15:0] out
);

always @ (posedge clk) begin
    out <= in;
end

endmodule

module pipeline_stage2 (
    input wire [7:0] in,
    input wire clk,
    output reg [7:0] out
);

always @ (posedge clk) begin
    out <= in;
end

endmodule
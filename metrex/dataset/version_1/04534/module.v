
module pipeline_split(
    input wire [15:0] in,
    output reg [7:0] out_hi,
    output reg [7:0] out_lo
);

always @(*) begin
    out_hi = in[15:8];
    out_lo = in[7:0];
end

endmodule
module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    input wire clk
); // Added clk as an input to the module

wire [7:0] stage1_out_hi;
wire [7:0] stage1_out_lo;

pipeline_split u_pipeline_split(
    .in(in),
    .out_hi(stage1_out_hi),
    .out_lo(stage1_out_lo)
);

// Added a register to pipeline the output
reg [7:0] out_hi_reg;
reg [7:0] out_lo_reg;

always @ (posedge clk) begin
  // Store the pipeline output in registers
  out_hi_reg <= stage1_out_hi;
  out_lo_reg <= stage1_out_lo;
end

assign out_hi = out_hi_reg;
assign out_lo = out_lo_reg;

endmodule
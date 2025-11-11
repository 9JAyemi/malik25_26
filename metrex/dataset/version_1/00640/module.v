
module FpuFp32(
    input clk,
    input [3:0] opMode,
    input [31:0] srca,
    input [31:0] srcb,
    output [31:0] dst
);

// Parameter definitions
parameter [3:0] OP_NONE = 4'h00;
parameter [3:0] OP_ADD = 4'h01;
parameter [3:0] OP_SUB = 4'h02;
parameter [3:0] OP_MUL = 4'h03;
parameter [3:0] OP_DIV = 4'h04;
parameter [3:0] OP_ABS = 4'h05;
parameter [3:0] OP_NEG = 4'h06;
parameter [3:0] OP_RCP = 4'h07;
parameter [3:0] OP_SQRT = 4'h08;

// Internal signals
wire fpaIsSub;
wire [31:0] fpaDst;
wire [31:0] fpmSrcB;
wire [31:0] fpmDst;
wire [31:0] fpRcpDst;

// Instantiate submodules
FpuFp32Add fpadd(clk, fpaIsSub, srca, srcb, fpaDst);
FpuFp32Mul fpmul(clk, srca, fpmSrcB, fpmDst);
FpuFp32Rcp fprcp(clk, srcb, fpRcpDst);

// Assign inputs to submodules
assign fpaIsSub = (opMode == OP_SUB);
assign fpmSrcB = (opMode == OP_DIV) ? fpRcpDst : srcb;

// Output selection logic
assign dst = (opMode == OP_ADD) ? fpaDst :
             (opMode == OP_SUB) ? fpaDst :
             (opMode == OP_MUL) ? fpmDst :
             (opMode == OP_DIV) ? fpmDst :
             (opMode == OP_ABS) ? ((srcb[31] == 1) ? -srcb : srcb) :
             (opMode == OP_NEG) ? -srcb :
             (opMode == OP_RCP) ? fpRcpDst :
             (opMode == OP_SQRT) ? ((srcb - 32'h3F80_0000) >>> 1) + 32'h3F80_0000 :
             srcb;

endmodule

module FpuFp32Add(clk, isSub, srca, srcb, dst);

input clk;
input isSub;
input [31:0] srca;
input [31:0] srcb;

output [31:0] dst;

reg [31:0] dst_reg;

always @ (posedge clk) begin
    if (isSub) begin
        dst_reg = srca - srcb;
    end else begin
        dst_reg = srca + srcb;
    end
end

assign dst = dst_reg;

endmodule

module FpuFp32Mul(clk, srca, srcb, dst);

input clk;
input [31:0] srca;
input [31:0] srcb;

output [31:0] dst;

reg [31:0] dst_reg;

always @ (posedge clk) begin
    dst_reg = srca * srcb;
end

assign dst = dst_reg;

endmodule

module FpuFp32Rcp(clk, srcb, dst);

input clk;
input [31:0] srcb;

output [31:0] dst;

reg [31:0] dst_reg;

always @ (posedge clk) begin
    dst_reg = 32'h3F80_0000 / srcb;
end

assign dst = dst_reg;

endmodule

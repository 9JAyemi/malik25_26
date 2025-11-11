module add_sub (
    input [15:0] A,
    input [15:0] B,
    input CTRL,
    output [15:0] SUM_DIFF,
    output CARRY_OUT_BORROW_OUT
);

reg [15:0] A_reg, B_reg, SUM_DIFF_reg;
reg CTRL_reg;
reg CARRY_IN_reg, BORROW_IN_reg;
wire CARRY_OUT, BORROW_OUT;

assign CARRY_OUT_BORROW_OUT = (CTRL == 0) ? CARRY_OUT : BORROW_OUT;

pipeline_stage1 stage1 (
    .A(A),
    .B(B),
    .CTRL(CTRL),
    .A_reg(A_reg),
    .B_reg(B_reg),
    .CTRL_reg(CTRL_reg),
    .CARRY_IN_reg(CARRY_IN_reg),
    .BORROW_IN_reg(BORROW_IN_reg)
);

pipeline_stage2 stage2 (
    .A_reg(A_reg),
    .B_reg(B_reg),
    .CTRL_reg(CTRL_reg),
    .CARRY_IN_reg(CARRY_IN_reg),
    .BORROW_IN_reg(BORROW_IN_reg),
    .SUM_DIFF_reg(SUM_DIFF_reg),
    .CARRY_OUT(CARRY_OUT),
    .BORROW_OUT(BORROW_OUT)
);

pipeline_stage3 stage3 (
    .SUM_DIFF_reg(SUM_DIFF_reg),
    .CARRY_OUT(CARRY_OUT),
    .BORROW_OUT(BORROW_OUT),
    .SUM_DIFF(SUM_DIFF)
);

endmodule

module pipeline_stage1 (
    input [15:0] A,
    input [15:0] B,
    input CTRL,
    output reg [15:0] A_reg,
    output reg [15:0] B_reg,
    output reg CTRL_reg,
    output reg CARRY_IN_reg,
    output reg BORROW_IN_reg
);

always @(A, B, CTRL) begin
    A_reg <= A;
    B_reg <= B;
    CTRL_reg <= CTRL;
    CARRY_IN_reg <= 1'b0;
    BORROW_IN_reg <= 1'b0;
end

endmodule

module pipeline_stage2 (
    input [15:0] A_reg,
    input [15:0] B_reg,
    input CTRL_reg,
    input CARRY_IN_reg,
    input BORROW_IN_reg,
    output reg [15:0] SUM_DIFF_reg,
    output reg CARRY_OUT,
    output reg BORROW_OUT
);

always @(A_reg, B_reg, CTRL_reg, CARRY_IN_reg, BORROW_IN_reg) begin
    if (CTRL_reg == 0) begin
        {CARRY_OUT, SUM_DIFF_reg} <= A_reg + B_reg + CARRY_IN_reg;
        BORROW_OUT <= (A_reg < B_reg) || ((A_reg == B_reg) && (CARRY_IN_reg == 1'b1));
    end else begin
        {BORROW_OUT, SUM_DIFF_reg} <= A_reg - B_reg - BORROW_IN_reg;
        CARRY_OUT <= (A_reg >= B_reg) && ((A_reg != B_reg) || (BORROW_IN_reg == 1'b1));
    end
end

endmodule

module pipeline_stage3 (
    input [15:0] SUM_DIFF_reg,
    input CARRY_OUT,
    input BORROW_OUT,
    output [15:0] SUM_DIFF
);

assign SUM_DIFF = SUM_DIFF_reg;

endmodule
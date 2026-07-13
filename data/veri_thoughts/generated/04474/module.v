
module MEMWB_Stage(
    input  clock,
    input  reset,
    input  M_Flush,
    input  M_Stall,
    input  WB_Stall,
    // Control Signals
    input  M_RegWrite,
    input  M_MemtoReg,
    // Data Signals
    input  [31:0] M_ReadData,
    input  [31:0] M_ALU_Result,
    input  [4:0]  M_RtRd,
    // Voter Signals for Registers
    input WB_RegWrite,
    input WB_MemtoReg,
    input [31:0] WB_ReadData,
    input [31:0] WB_ALU_Result,
    input [4:0]  WB_RtRd,
    output reg vote_WB_RegWrite = 1'b0,
    output reg vote_WB_MemtoReg = 1'b0,
    output reg [31:0] vote_WB_ReadData = 32'b0,
    output reg [31:0] vote_WB_ALU_Result = 32'b0,
    output reg [4:0]  vote_WB_RtRd = 5'b0
);

    // Update the pipeline register
    always @(posedge clock) begin
        if (reset) begin
            vote_WB_RegWrite <= 1'b0;
            vote_WB_MemtoReg <= 1'b0;
            vote_WB_ReadData <= 32'b0;
            vote_WB_ALU_Result <= 32'b0;
            vote_WB_RtRd <= 5'b0;
        end
        else begin
            if (!WB_Stall) begin
                vote_WB_RegWrite <= WB_RegWrite;
                vote_WB_MemtoReg <= WB_MemtoReg;
                vote_WB_ReadData <= WB_ReadData;
                vote_WB_ALU_Result <= WB_ALU_Result;
                vote_WB_RtRd <= WB_RtRd;
            end
            else if (M_Stall | M_Flush) begin
                vote_WB_RegWrite <= 1'b0;
                vote_WB_MemtoReg <= 1'b0;
                vote_WB_ReadData <= 32'b0;
                vote_WB_ALU_Result <= 32'b0;
                vote_WB_RtRd <= 5'b0;
            end
            else begin
                vote_WB_RegWrite <= M_RegWrite;
                vote_WB_MemtoReg <= M_MemtoReg;
                vote_WB_ReadData <= M_ReadData;
                vote_WB_ALU_Result <= M_ALU_Result;
                vote_WB_RtRd <= M_RtRd;
            end
        end
    end

endmodule
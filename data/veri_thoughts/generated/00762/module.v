module pipeline_register(
    input clock,
    input reset,
    input IF_Flush,
    input IF_Stall,
    input ID_Stall,
    input [31:0] IF_Instruction,
    input [31:0] IF_PCAdd4,
    input [31:0] IF_PC,
    input IF_IsBDS,
    input [31:0] ID_Instruction,
    input [31:0] ID_PCAdd4,
    input [31:0] ID_RestartPC,
    input ID_IsBDS,
    input ID_IsFlushed,
    output reg [31:0] vote_ID_Instruction,
    output reg [31:0] vote_ID_PCAdd4,
    output reg [31:0] vote_ID_RestartPC,
    output reg vote_ID_IsBDS,
    output reg vote_ID_IsFlushed
);

    always @(posedge clock) begin
        if (reset) begin
            vote_ID_Instruction <= 32'b0;
            vote_ID_PCAdd4 <= 32'b0;
            vote_ID_RestartPC <= 32'b0;
            vote_ID_IsBDS <= 1'b0;
            vote_ID_IsFlushed <= 1'b0;
        end else begin
            if (ID_Stall) begin
                vote_ID_Instruction <= ID_Instruction;
                vote_ID_PCAdd4 <= ID_PCAdd4;
                vote_ID_IsBDS <= ID_IsBDS;
                vote_ID_RestartPC <= ID_RestartPC;
                vote_ID_IsFlushed <= ID_IsFlushed;
            end else begin
                if (IF_Stall | IF_Flush) begin
                    vote_ID_Instruction <= 32'b0;
                    vote_ID_PCAdd4 <= 32'b0;
                end else begin
                    vote_ID_Instruction <= IF_Instruction;
                    vote_ID_PCAdd4 <= IF_PCAdd4;
                end
                if (ID_IsFlushed | IF_IsBDS) begin
                    vote_ID_RestartPC <= ID_RestartPC;
                end else begin
                    vote_ID_RestartPC <= IF_PC;
                end
                vote_ID_IsBDS <= ID_IsBDS;
                vote_ID_IsFlushed <= ID_IsFlushed;
            end
        end
    end

endmodule
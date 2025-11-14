module memoryaccess(
    output reg [31:0] ReadDataM, ALUResultOut, PCBranchM2,
    output reg [4:0] WriteRegM2, 
    output reg RegWriteM2, MemToRegM2, PCSrcM,
    input [31:0] WriteDataM, ALUResultIn, PCBranchM1,
    input [4:0] WriteRegM1,
    input BranchM, MemWriteM, MemToRegM1, RegWriteM1, ZerowireM, clk
);

    reg [31:0] mem[0:1023];

    always @(posedge clk) begin
        if (MemWriteM) begin
            mem[ALUResultIn[9:2]] <= WriteDataM;
        end
        if (MemToRegM1) begin
            ReadDataM <= mem[ALUResultIn[9:2]];
        end
        if (RegWriteM1) begin
            WriteRegM2 <= WriteRegM1;
        end
        RegWriteM2 <= RegWriteM1;
        MemToRegM2 <= MemToRegM1;
        ALUResultOut <= ALUResultIn;
        PCBranchM2 <= PCBranchM1;
        WriteRegM2 <= WriteRegM1;
        if (BranchM & ZerowireM) begin
            PCSrcM <= 1;
            PCBranchM2 <= PCBranchM1 + ALUResultIn;
        end else begin
            PCSrcM <= 0;
        end
    end

endmodule
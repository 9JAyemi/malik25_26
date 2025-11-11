module pipeline_processor(
    input clk, PCSrc,
    input [31:0] EX_MEM_NPC, IF_ID_IR, IF_ID_NPC,
    output reg [31:0] ID_EX_IR, ID_EX_A, ID_EX_B, ID_EX_NPC,
    output reg ID_EX_Flush
);

reg [31:0] reg_file[31:0];
reg [31:0] mem[1023:0];
reg [31:0] PC;

localparam ADD_OP = 5'b00000;
localparam SUB_OP = 5'b00001;
localparam LW_OP = 5'b00010;
localparam SW_OP = 5'b00011;
localparam BEQ_OP = 5'b00100;

localparam ST_IF = 2'b00;
localparam ST_ID = 2'b01;
localparam ST_EX = 2'b10;

reg [1:0] state;
reg [31:0] ID_EX_IR_temp, ID_EX_NPC_temp;
reg [4:0] ID_EX_rs, ID_EX_rt, ID_EX_rd, ID_EX_imm, ID_EX_func;
reg [2:0] ID_EX_ALUOp;
reg [31:0] ID_EX_A_temp, ID_EX_B_temp;

always @(posedge clk) begin
    if (state == ST_IF) begin
        ID_EX_Flush <= 0;
        ID_EX_IR_temp <= IF_ID_IR;
        ID_EX_NPC_temp <= IF_ID_NPC;
        PC <= IF_ID_NPC;
        state <= ST_ID;
    end else if (state == ST_ID) begin
        ID_EX_IR <= ID_EX_IR_temp;
        ID_EX_NPC <= ID_EX_NPC_temp;
        ID_EX_rs <= ID_EX_IR_temp[25:21];
        ID_EX_rt <= ID_EX_IR_temp[20:16];
        ID_EX_rd <= ID_EX_IR_temp[15:11];
        ID_EX_imm <= ID_EX_IR_temp[15:0];
        ID_EX_func <= ID_EX_IR_temp[5:0];
        ID_EX_A_temp <= reg_file[ID_EX_rs];
        ID_EX_B_temp <= reg_file[ID_EX_rt];
        case (ID_EX_IR_temp[31:26])
            ADD_OP, SUB_OP: ID_EX_ALUOp <= 3'b000;
            LW_OP: ID_EX_ALUOp <= 3'b001;
            SW_OP: ID_EX_ALUOp <= 3'b010;
            BEQ_OP: ID_EX_ALUOp <= 3'b100;
        endcase
        state <= ST_EX;
    end else if (state == ST_EX) begin
        ID_EX_A <= ID_EX_A_temp;
        ID_EX_B <= ID_EX_B_temp;
        case (ID_EX_ALUOp)
            3'b000: ID_EX_IR <= {6'b000000, ID_EX_rs, ID_EX_rt, ID_EX_rd, 5'b00000, ID_EX_func};
            3'b001: ID_EX_IR <= {6'b100011, ID_EX_rs, ID_EX_rt, ID_EX_imm};
            3'b010: ID_EX_IR <= {6'b101011, ID_EX_rs, ID_EX_rt, ID_EX_imm};
            3'b100: begin
                if (ID_EX_A_temp == ID_EX_B_temp) begin
                    ID_EX_Flush <= 1;
                    ID_EX_NPC <= ID_EX_NPC + (ID_EX_imm << 2);
                end else begin
                    ID_EX_Flush <= 0;
                    ID_EX_NPC <= ID_EX_NPC + 4;
                end
            end
        endcase
        state <= ST_IF;
        if (PCSrc == 1 || ID_EX_Flush == 1) begin
            PC <= EX_MEM_NPC;
        end else begin
            PC <= ID_EX_NPC;
        end
    end
end

always @(posedge clk) begin
    if (state == ST_EX) begin
        case (ID_EX_ALUOp)
            3'b000: reg_file[ID_EX_rd] <= ID_EX_A_temp + ID_EX_B_temp;
            3'b001: reg_file[ID_EX_rt] <= mem[ID_EX_A_temp + ID_EX_imm];
            3'b010: mem[ID_EX_A_temp + ID_EX_imm] <= ID_EX_B_temp;
        endcase
    end
end

endmodule
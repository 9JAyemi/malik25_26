
module pipeline (
  input clk,
  input reset,
  input [31:0] data1,
  input [31:0] data2,
  input [7:0] instruction,
  input [2:0] stage,
  input [3:0] rs1,
  input [3:0] rs2,
  input [3:0] rd,
  output [31:0] regfile_0,
  output [31:0] regfile_1,
  output [31:0] regfile_2,
  output [31:0] regfile_3,
  output [31:0] regfile_4,
  output [31:0] regfile_5,
  output [31:0] regfile_6,
  output [31:0] regfile_7,
  output [31:0] regfile_8,
  output [31:0] regfile_9,
  output [31:0] regfile_10,
  output [31:0] regfile_11,
  output [31:0] regfile_12,
  output [31:0] regfile_13,
  output [31:0] regfile_14,
  output [31:0] regfile_15
);

reg [31:0] pc;
reg [31:0] instruction_reg;
reg [31:0] alu_result;
reg [31:0] data2_reg;
reg [4:0] rs1_reg;
reg [4:0] rs2_reg;
reg [4:0] rd_reg;
reg [1:0] stage_reg;

assign regfile_0 = regfile[0];
assign regfile_1 = regfile[1];
assign regfile_2 = regfile[2];
assign regfile_3 = regfile[3];
assign regfile_4 = regfile[4];
assign regfile_5 = regfile[5];
assign regfile_6 = regfile[6];
assign regfile_7 = regfile[7];
assign regfile_8 = regfile[8];
assign regfile_9 = regfile[9];
assign regfile_10 = regfile[10];
assign regfile_11 = regfile[11];
assign regfile_12 = regfile[12];
assign regfile_13 = regfile[13];
assign regfile_14 = regfile[14];
assign regfile_15 = regfile[15];

reg [31:0] regfile [15:0];

always @(posedge clk) begin
  if (reset) begin
    pc <= 0;
    instruction_reg <= 0;
    alu_result <= 0;
    data2_reg <= 0;
    rs1_reg <= 0;
    rs2_reg <= 0;
    rd_reg <= 0;
    stage_reg <= 0;
  end else begin
    case (stage_reg)
      0: begin // Instruction Fetch
        instruction_reg <= instruction;
        pc <= pc + 1;
        stage_reg <= 1;
      end
      1: begin // Instruction Decode and Execution
        rs1_reg <= rs1;
        rs2_reg <= rs2;
        rd_reg <= rd;
        data2_reg <= data2;
        case (instruction_reg[7:0])
          8'h00: alu_result <= data1 + data2_reg; // ADD
          8'h01: alu_result <= data1 - data2_reg; // SUB
          8'h02: alu_result <= data1 & data2_reg; // AND
          8'h03: alu_result <= data1 | data2_reg; // OR
          8'h04: alu_result <= data1 ^ data2_reg; // XOR
          8'h05: alu_result <= ~data1; // NOT
          8'h06: alu_result <= data1 << data2_reg; // SLL
          8'h07: alu_result <= data1 >> data2_reg; // SRL
          default: alu_result <= 0;
        endcase
        stage_reg <= 2;
      end
      2: begin // Write Back
        regfile[rd_reg] <= alu_result;
        stage_reg <= 0;
      end
      default: stage_reg <= 0;
    endcase
  end
end

endmodule
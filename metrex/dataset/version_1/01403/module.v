
module pipeline (
  input clk,
  input reset,
  input [15:0] instruction,
  input [2:0] reg1_addr,
  input [2:0] reg2_addr,
  input [2:0] reg3_addr,
  input [15:0] reg1_data,
  input [15:0] reg2_data,
  input [15:0] reg3_data,
  output reg [15:0] reg1_out,
  output reg [15:0] reg2_out,
  output reg [15:0] reg3_out
);

reg [15:0] inst1, inst2, inst3;
reg [2:0] reg1_addr1, reg2_addr1, reg3_addr1;
reg [2:0] reg1_addr2, reg2_addr2, reg3_addr2;
reg [2:0] reg1_addr3, reg2_addr3, reg3_addr3;
reg [15:0] reg1_data1, reg2_data1, reg3_data1;
reg [15:0] reg1_data2, reg2_data2, reg3_data2;
reg [15:0] reg1_data3, reg2_data3, reg3_data3;

always @(posedge clk or posedge reset) begin
  if (reset) begin
    inst1 <= 16'h0;
    inst2 <= 16'h0;
    inst3 <= 16'h0;
    reg1_addr1 <= 3'b0;
    reg2_addr1 <= 3'b0;
    reg3_addr1 <= 3'b0;
    reg1_data1 <= 16'h0;
    reg2_data1 <= 16'h0;
    reg3_data1 <= 16'h0;
  end else begin
    inst1 <= instruction;
    inst2 <= inst1;
    inst3 <= inst2;
    reg1_addr1 <= reg1_addr;
    reg2_addr1 <= reg2_addr;
    reg3_addr1 <= reg3_addr;
    reg1_data1 <= reg1_data;
    reg2_data1 <= reg2_data;
    reg3_data1 <= reg3_data;
  end
end

always @(posedge clk or posedge reset) begin
  if (reset) begin
    reg1_addr2 <= 3'b0;
    reg2_addr2 <= 3'b0;
    reg3_addr2 <= 3'b0;
    reg1_data2 <= 16'h0;
    reg2_data2 <= 16'h0;
    reg3_data2 <= 16'h0;
  end else begin
    reg1_addr2 <= reg1_addr1;
    reg2_addr2 <= reg2_addr1;
    reg3_addr2 <= reg3_addr1;
    reg1_data2 <= reg1_data1;
    reg2_data2 <= reg2_data1;
    reg3_data2 <= reg3_data1;
  end
end

always @(posedge clk or posedge reset) begin
  if (reset) begin
    reg1_addr3 <= 3'b0;
    reg2_addr3 <= 3'b0;
    reg3_addr3 <= 3'b0;
    reg1_data3 <= 16'h0;
    reg2_data3 <= 16'h0;
    reg3_data3 <= 16'h0;
  end else begin
    reg1_addr3 <= reg1_addr2;
    reg2_addr3 <= reg2_addr2;
    reg3_addr3 <= reg3_addr2;
    reg1_data3 <= reg1_data2;
    reg2_data3 <= reg2_data2;
    reg3_data3 <= reg3_data2;

    case (inst3[15:13])
      3'b000: reg1_out <= reg1_data3 + reg2_data3;
      3'b001: reg1_out <= reg1_data3 - reg2_data3;
      3'b010: reg1_out <= reg1_data3 & reg2_data3;
      3'b011: reg1_out <= reg1_data3 | reg2_data3;
      3'b100: reg1_out <= reg1_data3 ^ reg2_data3;
    endcase

    case (inst2[15:13])
      3'b000: reg2_out <= reg2_data3 + reg3_data3;
      3'b001: reg2_out <= reg2_data3 - reg3_data3;
      3'b010: reg2_out <= reg2_data3 & reg3_data3;
      3'b011: reg2_out <= reg2_data3 | reg3_data3;
      3'b100: reg2_out <= reg2_data3 ^ reg3_data3;
    endcase

    case (inst1[15:13])
      3'b000: reg3_out <= reg3_data3 + reg1_data3;
      3'b001: reg3_out <= reg3_data3 - reg1_data3;
      3'b010: reg3_out <= reg3_data3 & reg1_data3;
      3'b011: reg3_out <= reg3_data3 | reg1_data3;
      3'b100: reg3_out <= reg3_data3 ^ reg1_data3;
    endcase
  end
end

endmodule

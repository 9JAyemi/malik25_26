

module EXMEMreg(clk,Rtin,Rdin,PCplusin,ALUresultin,DatabusBin,RegDstin,RegWrin,MemWrin,MemRdin,MemtoRegin,
Rtout,Rdout,PCplusout,ALUresultout,DatabusBout,RegDstout,RegWrout,MemWrout,MemRdout,MemtoRegout);

input clk;
input [4:0] Rtin;
input [4:0] Rdin;
input [31:0] PCplusin;
input [31:0] ALUresultin;
input [31:0] DatabusBin;
input [1:0] RegDstin;
input RegWrin;
input MemWrin;
input MemRdin;
input [1:0] MemtoRegin;
output [4:0] Rtout;
reg [4:0] Rtout;
output [4:0] Rdout;
reg [4:0] Rdout;
output [31:0] PCplusout;
reg [31:0] PCplusout;
output [31:0] ALUresultout;
reg [31:0] ALUresultout;
output [31:0] DatabusBout;
reg [31:0] DatabusBout;
output [1:0] RegDstout;
reg [1:0] RegDstout;
output RegWrout;
reg RegWrout;
output MemWrout;
reg MemWrout;
output MemRdout;
reg MemRdout;
output [1:0] MemtoRegout;
reg [1:0] MemtoRegout;

always @(posedge clk)
begin
  Rtout <= Rtin;
  Rdout <= Rdin;
  PCplusout <= PCplusin;
  ALUresultout <= ALUresultin;
  DatabusBout <= DatabusBin;
  RegDstout <= RegDstin;
  RegWrout <= RegWrin;
  MemWrout <= MemWrin;
  MemRdout <= MemRdin;
  MemtoRegout <= MemtoRegin;
end

endmodule

module mul_16_32_mult
   (CLK,
    A,
    B,
    CE,
    SCLR,
    ZERO_DETECT,
    P,
    PCASC);
  input CLK;
  input [15:0]A;
  input [31:0]B;
  input CE;
  input SCLR;
  output [1:0]ZERO_DETECT;
  output [47:0]P;
  output [47:0]PCASC;

  reg [15:0] A_reg;
  reg [31:0] B_reg;
  reg [47:0] P_reg;
  reg [47:0] PCASC_reg;
  reg [1:0] ZERO_DETECT_reg;
  wire [15:0] A_shifted;
  wire [31:0] B_shifted;
  wire [47:0] P_shifted;
  wire [47:0] PCASC_shifted;

  assign A_shifted = {16'b0, A};
  assign B_shifted = {16'b0, B};
  assign P_shifted = {32'b0, P_reg};
  assign PCASC_shifted = {32'b0, PCASC_reg};

  always @(posedge CLK) begin
    if (SCLR) begin
      A_reg <= 16'b0;
      B_reg <= 32'b0;
      P_reg <= 48'b0;
      PCASC_reg <= 48'b0;
      ZERO_DETECT_reg <= 2'b11;
    end else if (CE) begin
      A_reg <= A;
      B_reg <= B;
      P_reg <= P_shifted + (A_shifted * B_shifted);
      PCASC_reg <= PCASC_shifted + ({32'b0, A} * B_shifted);
      ZERO_DETECT_reg <= (P_reg == 48'b0) ? 2'b11 : (P_reg[47:0] == 0) ? 2'b10 : 2'b00;
    end
  end

  assign P = P_reg;
  assign PCASC = PCASC_reg;
  assign ZERO_DETECT = ZERO_DETECT_reg;

endmodule
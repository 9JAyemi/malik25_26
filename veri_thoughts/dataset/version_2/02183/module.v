module chatgpt_generate_JC_counter(
  input                clk,
  input                rst_n,
  output reg  [63:0]   Q
);

  wire [63:0] Qn;
  
  assign Qn[0] = ~Q[63];
  assign Qn[1] = Q[0] ^ Q[63];
  assign Qn[2] = Q[1] ^ Q[63];
  assign Qn[3] = Q[2] ^ Q[63];
  assign Qn[4] = Q[3] ^ Q[63];
  assign Qn[5] = Q[4] ^ Q[63];
  assign Qn[6] = Q[5] ^ Q[63];
  assign Qn[7] = Q[6] ^ Q[63];
  assign Qn[8] = Q[7] ^ Q[63];
  assign Qn[9] = Q[8] ^ Q[63];
  assign Qn[10] = Q[9] ^ Q[63];
  assign Qn[11] = Q[10] ^ Q[63];
  assign Qn[12] = Q[11] ^ Q[63];
  assign Qn[13] = Q[12] ^ Q[63];
  assign Qn[14] = Q[13] ^ Q[63];
  assign Qn[15] = Q[14] ^ Q[63];
  assign Qn[16] = Q[15] ^ Q[63];
  assign Qn[17] = Q[16] ^ Q[63];
  assign Qn[18] = Q[17] ^ Q[63];
  assign Qn[19] = Q[18] ^ Q[63];
  assign Qn[20] = Q[19] ^ Q[63];
  assign Qn[21] = Q[20] ^ Q[63];
  assign Qn[22] = Q[21] ^ Q[63];
  assign Qn[23] = Q[22] ^ Q[63];
  assign Qn[24] = Q[23] ^ Q[63];
  assign Qn[25] = Q[24] ^ Q[63];
  assign Qn[26] = Q[25] ^ Q[63];
  assign Qn[27] = Q[26] ^ Q[63];
  assign Qn[28] = Q[27] ^ Q[63];
  assign Qn[29] = Q[28] ^ Q[63];
  assign Qn[30] = Q[29] ^ Q[63];
  assign Qn[31] = Q[30] ^ Q[63];
  assign Qn[32] = Q[31] ^ Q[63];
  assign Qn[33] = Q[32] ^ Q[63];
  assign Qn[34] = Q[33] ^ Q[63];
  assign Qn[35] = Q[34] ^ Q[63];
  assign Qn[36] = Q[35] ^ Q[63];
  assign Qn[37] = Q[36] ^ Q[63];
  assign Qn[38] = Q[37] ^ Q[63];
  assign Qn[39] = Q[38] ^ Q[63];
  assign Qn[40] = Q[39] ^ Q[63];
  assign Qn[41] = Q[40] ^ Q[63];
  assign Qn[42] = Q[41] ^ Q[63];
  assign Qn[43] = Q[42] ^ Q[63];
  assign Qn[44] = Q[43] ^ Q[63];
  assign Qn[45] = Q[44] ^ Q[63];
  assign Qn[46] = Q[45] ^ Q[63];
  assign Qn[47] = Q[46] ^ Q[63];
  assign Qn[48] = Q[47] ^ Q[63];
  assign Qn[49] = Q[48] ^ Q[63];
  assign Qn[50] = Q[49] ^ Q[63];
  assign Qn[51] = Q[50] ^ Q[63];
  assign Qn[52] = Q[51] ^ Q[63];
  assign Qn[53] = Q[52] ^ Q[63];
  assign Qn[54] = Q[53] ^ Q[63];
  assign Qn[55] = Q[54] ^ Q[63];
  assign Qn[56] = Q[55] ^ Q[63];
  assign Qn[57] = Q[56] ^ Q[63];
  assign Qn[58] = Q[57] ^ Q[63];
  assign Qn[59] = Q[58] ^ Q[63];
  assign Qn[60] = Q[59] ^ Q[63];
  assign Qn[61] = Q[60] ^ Q[63];
  assign Qn[62] = Q[61] ^ Q[63];
  assign Qn[63] = Q[62];
  
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      Q <= 64'h0000000000000001;
    end
    else begin
      Q <= Qn;
    end
  end
  
endmodule


module GenPP_32Bits(PP15,PP14,PP13,PP12,PP11,PP10,PP9,PP8,
                    PP7,PP6,PP5,PP4,PP3,PP2,PP1,PP0,iso_X,iso_Y,iso_in);
  `define nBits 32

  output [`nBits:0]      PP15;                   output [`nBits:0]      PP14;                   output [`nBits:0]      PP13;                   output [`nBits:0]      PP12;                   output [`nBits:0]      PP11;                   output [`nBits:0]      PP10;                   output [`nBits:0]      PP9;                    output [`nBits:0]      PP8;                    output [`nBits:0]      PP7;                    output [`nBits:0]      PP6;                    output [`nBits:0]      PP5;                    output [`nBits:0]      PP4;                    output [`nBits:0]      PP3;                    output [`nBits:0]      PP2;                    output [`nBits:0]      PP1;                    output [`nBits:0]      PP0;                    input  [`nBits-1:0]    iso_X;                      input  [`nBits-1:0]    iso_Y;                      input                iso_in;
  wire                 iso_in_N;
  wire [`nBits-1:0]    X;
  wire [`nBits-1:0]    Y;

  wire [2:0] Seg15 = Y[31:29];           wire [2:0] Seg14 = Y[29:27];           wire [2:0] Seg13 = Y[27:25];           wire [2:0] Seg12 = Y[25:23];           wire [2:0] Seg11 = Y[23:21];           wire [2:0] Seg10 = Y[21:19];           wire [2:0] Seg9  = Y[19:17];           wire [2:0] Seg8  = Y[17:15];           wire [2:0] Seg7  = Y[15:13];           wire [2:0] Seg6  = Y[13:11];           wire [2:0] Seg5  = Y[11:9];            wire [2:0] Seg4  = Y[9:7];             wire [2:0] Seg3  = Y[7:5];             wire [2:0] Seg2  = Y[5:3];             wire [2:0] Seg1  = Y[3:1];             wire [2:0] Seg0  = {Y[1:0], 1'b0};     assign X = iso_X;
  assign Y = iso_Y;

  assign PP15[`nBits:0] = BoothDecode(Seg15[2:0],X[`nBits-1:0]);
  assign PP14[`nBits:0] = BoothDecode(Seg14[2:0],X[`nBits-1:0]);
  assign PP13[`nBits:0] = BoothDecode(Seg13[2:0],X[`nBits-1:0]);
  assign PP12[`nBits:0] = BoothDecode(Seg12[2:0],X[`nBits-1:0]);
  assign PP11[`nBits:0] = BoothDecode(Seg11[2:0],X[`nBits-1:0]);
  assign PP10[`nBits:0] = BoothDecode(Seg10[2:0],X[`nBits-1:0]);
  assign PP9[`nBits:0] = BoothDecode(Seg9[2:0],X[`nBits-1:0]);
  assign PP8[`nBits:0] = BoothDecode(Seg8[2:0],X[`nBits-1:0]);
  assign PP7[`nBits:0] = BoothDecode(Seg7[2:0],X[`nBits-1:0]);
  assign PP6[`nBits:0] = BoothDecode(Seg6[2:0],X[`nBits-1:0]);
  assign PP5[`nBits:0] = BoothDecode(Seg5[2:0],X[`nBits-1:0]);
  assign PP4[`nBits:0] = BoothDecode(Seg4[2:0],X[`nBits-1:0]);
  assign PP3[`nBits:0] = BoothDecode(Seg3[2:0],X[`nBits-1:0]);
  assign PP2[`nBits:0] = BoothDecode(Seg2[2:0],X[`nBits-1:0]);
  assign PP1[`nBits:0] = BoothDecode(Seg1[2:0],X[`nBits-1:0]);
  assign PP0[`nBits:0] = BoothDecode(Seg0[2:0],X[`nBits-1:0]);

  function [`nBits:0] BoothDecode;
    input [2:0] Segment;
    input [`nBits:0] X;
    case ( Segment[2:0] )
         3'b000  :  BoothDecode = 33'h000000000;                    3'b001,
         3'b010  :  BoothDecode = { X[`nBits-1], X[`nBits-1:0] }  ; 3'b011  :  BoothDecode = { X[`nBits-1:0], 1'b0  }  ;       3'b100  :  BoothDecode = { ~X[`nBits-1:0], 1'b1  }  ;      3'b101,
         3'b110  :  BoothDecode = { ~X[`nBits-1], ~X[`nBits-1:0] } ;3'b111  :  BoothDecode = 33'h1FFFFFFFF;                    endcase
  endfunction
endmodule

// SVA for control_digitos_1
module control_digitos_1_sva(
  input  logic        clk,
  input  logic [7:0]  estado,
  input  logic [3:0]  RG1_Dec, RG2_Dec, RG3_Dec,
  input  logic        escribiendo, en_out,
  input  logic [3:0]  dig0_Dec, direccion,
  input  logic [3:0]  dig_Dec_Ho, dig_Dec_min, dig_Dec_seg,
                      dig_Dec_mes, dig_Dec_dia, dig_Dec_an,
                      dig_Dec_Ho_Ti, dig_Dec_min_Ti, dig_Dec_seg_Ti
);

  default clocking @(posedge clk); endclocking

  localparam logic [3:0] ADDR_HO     = 4'h0;
  localparam logic [3:0] ADDR_MIN    = 4'h1;
  localparam logic [3:0] ADDR_SEG    = 4'h2;
  localparam logic [3:0] ADDR_MES    = 4'h3;
  localparam logic [3:0] ADDR_DIA    = 4'h4;
  localparam logic [3:0] ADDR_AN     = 4'h5;
  localparam logic [3:0] ADDR_HO_Ti  = 4'h6;
  localparam logic [3:0] ADDR_MIN_Ti = 4'h7;
  localparam logic [3:0] ADDR_SEG_Ti = 4'h8;

  let en_out_wr = (~escribiendo && en_out &&
                   (direccion inside {ADDR_HO,ADDR_MIN,ADDR_SEG,ADDR_MES,ADDR_DIA,ADDR_AN,ADDR_HO_Ti,ADDR_MIN_Ti,ADDR_SEG_Ti}));
  let es7d_wr   = (escribiendo && estado==8'h7d && (direccion inside {ADDR_MES,ADDR_DIA,ADDR_AN}));
  let es6c_wr   = (escribiendo && estado==8'h6c && (direccion inside {ADDR_HO,ADDR_MIN,ADDR_SEG}));
  let es75_wr   = (escribiendo && estado==8'h75 && (direccion inside {ADDR_HO_Ti,ADDR_MIN_Ti,ADDR_SEG_Ti}));

  let hold_all = (
      dig_Dec_Ho     == $past(dig_Dec_Ho)     &&
      dig_Dec_min    == $past(dig_Dec_min)    &&
      dig_Dec_seg    == $past(dig_Dec_seg)    &&
      dig_Dec_mes    == $past(dig_Dec_mes)    &&
      dig_Dec_dia    == $past(dig_Dec_dia)    &&
      dig_Dec_an     == $past(dig_Dec_an)     &&
      dig_Dec_Ho_Ti  == $past(dig_Dec_Ho_Ti)  &&
      dig_Dec_min_Ti == $past(dig_Dec_min_Ti) &&
      dig_Dec_seg_Ti == $past(dig_Dec_seg_Ti)
  );

  // If no write condition is active, all outputs must hold
  assert property ( !(en_out_wr || es7d_wr || es6c_wr || es75_wr) |=> hold_all );

  // --- en_out path (~escribiendo) updates and "only-that-one" changes ---
  assert property ((~escribiendo && en_out && direccion==ADDR_HO)
      |=> dig_Dec_Ho==$past(dig0_Dec) &&
          dig_Dec_min==$past(dig_Dec_min) && dig_Dec_seg==$past(dig_Dec_seg) &&
          dig_Dec_mes==$past(dig_Dec_mes) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_MIN)
      |=> dig_Dec_min==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_seg==$past(dig_Dec_seg) &&
          dig_Dec_mes==$past(dig_Dec_mes) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_SEG)
      |=> dig_Dec_seg==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_mes==$past(dig_Dec_mes) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_MES)
      |=> dig_Dec_mes==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_DIA)
      |=> dig_Dec_dia==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_AN)
      |=> dig_Dec_an==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  // Special case for ADDR_HO_Ti: 0xF maps to 0
  assert property ((~escribiendo && en_out && direccion==ADDR_HO_Ti && dig0_Dec==4'hF)
      |=> dig_Dec_Ho_Ti==4'h0 &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_HO_Ti && dig0_Dec!=4'hF)
      |=> dig_Dec_Ho_Ti==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_MIN_Ti)
      |=> dig_Dec_min_Ti==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((~escribiendo && en_out && direccion==ADDR_SEG_Ti)
      |=> dig_Dec_seg_Ti==$past(dig0_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) && dig_Dec_min_Ti==$past(dig_Dec_min_Ti));

  // --- escribiendo path updates and "only-that-one" changes ---
  // estado 0x7d: MES<-RG2, DIA<-RG1, AN<-RG3
  assert property ((escribiendo && estado==8'h7d && direccion==ADDR_MES)
      |=> dig_Dec_mes==$past(RG2_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((escribiendo && estado==8'h7d && direccion==ADDR_DIA)
      |=> dig_Dec_dia==$past(RG1_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((escribiendo && estado==8'h7d && direccion==ADDR_AN)
      |=> dig_Dec_an==$past(RG3_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  // estado 0x6c: HO<-RG3, MIN<-RG2, SEG<-RG1
  assert property ((escribiendo && estado==8'h6c && direccion==ADDR_HO)
      |=> dig_Dec_Ho==$past(RG3_Dec) &&
          dig_Dec_min==$past(dig_Dec_min) && dig_Dec_seg==$past(dig_Dec_seg) &&
          dig_Dec_mes==$past(dig_Dec_mes) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((escribiendo && estado==8'h6c && direccion==ADDR_MIN)
      |=> dig_Dec_min==$past(RG2_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_seg==$past(dig_Dec_seg) &&
          dig_Dec_mes==$past(dig_Dec_mes) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((escribiendo && estado==8'h6c && direccion==ADDR_SEG)
      |=> dig_Dec_seg==$past(RG1_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_mes==$past(dig_Dec_mes) && dig_Dec_dia==$past(dig_Dec_dia) &&
          dig_Dec_an==$past(dig_Dec_an) && dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  // estado 0x75: HO_Ti<-RG3, MIN_Ti<-RG2, SEG_Ti<-RG1
  assert property ((escribiendo && estado==8'h75 && direccion==ADDR_HO_Ti)
      |=> dig_Dec_Ho_Ti==$past(RG3_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_min_Ti==$past(dig_Dec_min_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((escribiendo && estado==8'h75 && direccion==ADDR_MIN_Ti)
      |=> dig_Dec_min_Ti==$past(RG2_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) && dig_Dec_seg_Ti==$past(dig_Dec_seg_Ti));

  assert property ((escribiendo && estado==8'h75 && direccion==ADDR_SEG_Ti)
      |=> dig_Dec_seg_Ti==$past(RG1_Dec) &&
          dig_Dec_Ho==$past(dig_Dec_Ho) && dig_Dec_min==$past(dig_Dec_min) &&
          dig_Dec_seg==$past(dig_Dec_seg) && dig_Dec_mes==$past(dig_Dec_mes) &&
          dig_Dec_dia==$past(dig_Dec_dia) && dig_Dec_an==$past(dig_Dec_an) &&
          dig_Dec_Ho_Ti==$past(dig_Dec_Ho_Ti) && dig_Dec_min_Ti==$past(dig_Dec_min_Ti));

  // --- Coverage ---
  cover property (~escribiendo && en_out && direccion==ADDR_HO);
  cover property (~escribiendo && en_out && direccion==ADDR_MIN);
  cover property (~escribiendo && en_out && direccion==ADDR_SEG);
  cover property (~escribiendo && en_out && direccion==ADDR_MES);
  cover property (~escribiendo && en_out && direccion==ADDR_DIA);
  cover property (~escribiendo && en_out && direccion==ADDR_AN);
  cover property (~escribiendo && en_out && direccion==ADDR_HO_Ti && dig0_Dec==4'hF);
  cover property (~escribiendo && en_out && direccion==ADDR_HO_Ti && dig0_Dec!=4'hF);
  cover property (~escribiendo && en_out && direccion==ADDR_MIN_Ti);
  cover property (~escribiendo && en_out && direccion==ADDR_SEG_Ti);

  cover property (escribiendo && estado==8'h7d && direccion==ADDR_MES);
  cover property (escribiendo && estado==8'h7d && direccion==ADDR_DIA);
  cover property (escribiendo && estado==8'h7d && direccion==ADDR_AN);

  cover property (escribiendo && estado==8'h6c && direccion==ADDR_HO);
  cover property (escribiendo && estado==8'h6c && direccion==ADDR_MIN);
  cover property (escribiendo && estado==8'h6c && direccion==ADDR_SEG);

  cover property (escribiendo && estado==8'h75 && direccion==ADDR_HO_Ti);
  cover property (escribiendo && estado==8'h75 && direccion==ADDR_MIN_Ti);
  cover property (escribiendo && estado==8'h75 && direccion==ADDR_SEG_Ti);

  cover property (!(en_out_wr || es7d_wr || es6c_wr || es75_wr)); // hold cycle
endmodule

// Bind example:
// bind control_digitos_1 control_digitos_1_sva sva_inst(.*);
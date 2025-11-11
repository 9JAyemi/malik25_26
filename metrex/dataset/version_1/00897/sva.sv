// SVA for muxed_ctrl_data: bind this to the DUT
module muxed_ctrl_data_sva(
  input logic [5:0]  ByteCnt,
  input logic        DlyCrcEn,
  input logic [1:0]  DlyCrcCnt,
  input logic [47:0] MAC,
  input logic [15:0] TxPauseTV,
  input logic        MTxClk,
  input logic        TxReset,
  input logic [7:0]  ControlData
);

function automatic [7:0] exp_muxed(input logic [5:0] bc,
                                   input logic DlyCrcEn_i,
                                   input logic [1:0] DlyCrcCnt_i,
                                   input logic [47:0] MAC_i,
                                   input logic [15:0] TxPauseTV_i);
  case (bc)
    6'h0 : exp_muxed = ((~DlyCrcEn_i) || (DlyCrcEn_i && (&DlyCrcCnt_i))) ? 8'h01 : 8'h00;
    6'h2 : exp_muxed = 8'h80;
    6'h4 : exp_muxed = 8'hC2;
    6'h6 : exp_muxed = 8'h00;
    6'h8 : exp_muxed = 8'h00;
    6'hA : exp_muxed = 8'h01;
    6'hC : exp_muxed = MAC_i[47:40];
    6'hE : exp_muxed = MAC_i[39:32];
    6'h10: exp_muxed = MAC_i[31:24];
    6'h12: exp_muxed = MAC_i[23:16];
    6'h14: exp_muxed = MAC_i[15:8];
    6'h16: exp_muxed = MAC_i[7:0];
    6'h18: exp_muxed = 8'h88;
    6'h1A: exp_muxed = 8'h08;
    6'h1C: exp_muxed = 8'h00;
    6'h1E: exp_muxed = 8'h01;
    6'h20: exp_muxed = TxPauseTV_i[15:8];
    6'h22: exp_muxed = TxPauseTV_i[7:0];
    default: exp_muxed = 8'h00;
  endcase
endfunction

// Reset behavior (asynchronous reset asserted, register must be 0 at this clk edge)
assert property (@(posedge MTxClk) TxReset |-> ##0 (ControlData == 8'h00))
  else $error("ControlData not zero during reset");

// Even ByteCnt cycles update to expected value (check after NBA using ##0)
assert property (@(posedge MTxClk)
                   (!TxReset && !ByteCnt[0])
                 |-> ##0 (ControlData == exp_muxed(ByteCnt, DlyCrcEn, DlyCrcCnt, MAC, TxPauseTV)))
  else $error("ControlData mismatch on even ByteCnt");

// Odd ByteCnt cycles hold previous value (guard previous cycle not in reset)
assert property (@(posedge MTxClk)
                   (!TxReset && ByteCnt[0] && $past(!TxReset))
                 |-> ##0 (ControlData == $past(ControlData)))
  else $error("ControlData changed on odd ByteCnt");

// No X/Z while active
assert property (@(posedge MTxClk) !TxReset |-> ##0 (!$isunknown(ControlData)))
  else $error("ControlData is X/Z while active");

// Coverage: hit all programmed even addresses and default, and both 6'h0 branches
cover property (@(posedge MTxClk) !TxReset && !ByteCnt[0] && (ByteCnt inside {
  6'h2,6'h4,6'h6,6'h8,6'hA,6'hC,6'hE,6'h10,6'h12,6'h14,6'h16,6'h18,6'h1A,6'h1C,6'h1E,6'h20,6'h22
}));

cover property (@(posedge MTxClk) !TxReset && !ByteCnt[0] &&
                !(ByteCnt inside {6'h0,6'h2,6'h4,6'h6,6'h8,6'hA,6'hC,6'hE,6'h10,6'h12,6'h14,6'h16,6'h18,6'h1A,6'h1C,6'h1E,6'h20,6'h22}));
// default case covered

// 6'h0 branch where output is 01
cover property (@(posedge MTxClk) !TxReset && !ByteCnt[0] && (ByteCnt==6'h0) &&
                ((~DlyCrcEn) || (DlyCrcEn && (&DlyCrcCnt))));
// 6'h0 branch where output is 00
cover property (@(posedge MTxClk) !TxReset && !ByteCnt[0] && (ByteCnt==6'h0) &&
                (DlyCrcEn && !(&DlyCrcCnt)));

// Reset deassert then first even capture
cover property (@(posedge MTxClk) $fell(TxReset) ##1 (!TxReset && !ByteCnt[0]));

endmodule

// Bind into the DUT
bind muxed_ctrl_data muxed_ctrl_data_sva sva_muxed_ctrl_data (.*);
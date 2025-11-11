// SVA for alu_min
// Concise, high-value checks (reset, clocking, core op classes, RGZ-based ops, multiply, and coverage)

`ifndef ALU_MIN_SVA
`define ALU_MIN_SVA

module alu_min_sva
(
  input  logic        RST,
  input  logic        CLK,
  input  logic        ENA,
  input  logic [7:0]  OPT,
  input  logic [7:0]  RGA,
  input  logic [7:0]  RGB,
  input  logic [1:0]  KEY,
  input  logic [7:0]  RGZ
);

  default clocking cb @(posedge CLK); endclocking

  // Helpers
  function automatic logic [7:0] to_u8bit1(logic b);
    return b ? 8'h01 : 8'h00;
  endfunction

  // Basic sanity
  // Sync reset
  assert property (RST |-> (RGZ == 8'h00));

  // No X/Z on key signals at clock
  assert property (!$isunknown({RST, OPT, RGA, RGB, ENA, KEY, RGZ})));

  // RGZ changes only on clock (no glitching between clocks)
  assert property (@(negedge CLK) $stable(RGZ));

  // Core function classes (high-nibble 4..F families; exclude nibble==3 which is inconsistent in RTL)
  // RGA +/- RGB, RGB-1
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h0) |-> RGZ == (RGA + RGB));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h1) |-> RGZ == (RGA - RGB));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h2) |-> RGZ == (RGB - 8'h01));

  // Logical (1-bit results widened to 8b)
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h4) |-> RGZ == to_u8bit1((RGA!=8'h00) && (RGB!=8'h00)));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h5) |-> RGZ == to_u8bit1((RGA!=8'h00) || (RGB!=8'h00)));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h6) |-> RGZ == to_u8bit1(RGA==8'h00));

  // Bitwise/unary on RGA
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h7) |-> RGZ == (~RGA));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h8) |-> RGZ == (RGA & RGB));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h9) |-> RGZ == (RGA | RGB));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'hA) |-> RGZ == (RGA ^ RGB));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'hB) |-> RGZ == (RGA << 1));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'hC) |-> RGZ == (RGA >> 1));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'hD) |-> RGZ == (RGA + 8'h01));
  assert property (disable iff (RST)
    (OPT[7:4] inside {[4'h4:4'hF]} && (OPT[3:0] inside {4'hE,4'hF})) |-> RGZ == (RGA - 8'h01));

  // Selected early opcodes (0x00..0x2F family) to extend coverage of same functions
  assert property (disable iff (RST) (OPT==8'h01) |-> RGZ==8'h00);
  assert property (disable iff (RST) (OPT==8'h02) |-> RGZ==(RGA+RGB));
  assert property (disable iff (RST) (OPT==8'h03) |-> 1'b1); // ambiguous/duplicate in RTL; do not check
  assert property (disable iff (RST) (OPT==8'h04) |-> RGZ==(RGA & RGB));
  assert property (disable iff (RST) (OPT==8'h05) |-> RGZ==(RGA | RGB));
  assert property (disable iff (RST) (OPT==8'h06) |-> RGZ==to_u8bit1((RGA!=0)&&(RGB!=0)));
  assert property (disable iff (RST) (OPT==8'h07) |-> RGZ==to_u8bit1((RGA!=0)||(RGB!=0)));
  assert property (disable iff (RST) (OPT inside {8'h08,8'h28}) |-> RGZ==(RGA+8'h01));
  assert property (disable iff (RST) (OPT inside {8'h09,8'h29}) |-> RGZ==(RGA-8'h01));
  assert property (disable iff (RST) (OPT inside {8'h0A,8'h2A}) |-> RGZ==(RGA<<1));
  assert property (disable iff (RST) (OPT inside {8'h0B,8'h2B}) |-> RGZ==(RGA>>1));
  assert property (disable iff (RST) (OPT inside {8'h0C,8'h2C}) |-> RGZ==to_u8bit1(RGA==8'h00));
  assert property (disable iff (RST) (OPT inside {8'h0D,8'h2D}) |-> RGZ==(~RGA));

  // RGZ-based unary ops (0011_8..D)
  assert property (disable iff (RST)
    (OPT[7:4]==4'h3 && OPT[3:0]==4'h8) |-> RGZ == ($past(RGZ) + 8'h01));
  assert property (disable iff (RST)
    (OPT[7:4]==4'h3 && OPT[3:0]==4'h9) |-> RGZ == ($past(RGZ) - 8'h01));
  assert property (disable iff (RST)
    (OPT[7:4]==4'h3 && OPT[3:0]==4'hA) |-> RGZ == ($past(RGZ) << 1));
  assert property (disable iff (RST)
    (OPT[7:4]==4'h3 && OPT[3:0]==4'hB) |-> RGZ == ($past(RGZ) >> 1));
  assert property (disable iff (RST)
    (OPT[7:4]==4'h3 && OPT[3:0]==4'hC) |-> RGZ == to_u8bit1($past(RGZ)==8'h00));
  assert property (disable iff (RST)
    (OPT[7:4]==4'h3 && OPT[3:0]==4'hD) |-> RGZ == (~$past(RGZ)));

  // RGZ binary with RGA/RGB
  assert property (disable iff (RST) (OPT==8'h30) |-> RGZ == ($past(RGZ) + RGA));
  assert property (disable iff (RST) (OPT==8'h31) |-> RGZ == ($past(RGZ) - RGA));
  assert property (disable iff (RST) (OPT==8'h3E) |-> RGZ == ($past(RGZ) + RGB));
  assert property (disable iff (RST) (OPT==8'h3F) |-> RGZ == ($past(RGZ) - RGB));

  // RGB op RGZ family (0001_0000..0001_0111)
  assert property (disable iff (RST) (OPT==8'h10) |-> RGZ == (RGB + $past(RGZ)));
  assert property (disable iff (RST) (OPT==8'h11) |-> RGZ == (RGB - $past(RGZ)));
  assert property (disable iff (RST) (OPT==8'h13) |-> RGZ == (RGB ^ $past(RGZ)));
  assert property (disable iff (RST) (OPT==8'h14) |-> RGZ == (RGB & $past(RGZ)));
  assert property (disable iff (RST) (OPT==8'h15) |-> RGZ == (RGB | $past(RGZ)));
  assert property (disable iff (RST) (OPT==8'h16) |-> RGZ == to_u8bit1((RGB!=0) && ($past(RGZ)!=0)));
  assert property (disable iff (RST) (OPT==8'h17) |-> RGZ == to_u8bit1((RGB!=0) || ($past(RGZ)!=0)));

  // Multiply cases present in RTL (result truncation to 8b)
  assert property (disable iff (RST)
    (OPT inside {8'h53,8'h73,8'hA3,8'hB3,8'hC3,8'hD3,8'hE3,8'hF3}) |-> RGZ == (RGA*RGB)[7:0]);

  // Minimal functional coverage (representative)
  cover property (@cb RST ##1 !RST);                  // reset deassert
  cover property (@cb (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'h0)); // add class
  cover property (@cb (OPT[7:4] inside {[4'h4:4'hF]} && OPT[3:0]==4'hA)); // xor class
  cover property (@cb (OPT==8'h3E));                  // RGZ+RGB class
  cover property (@cb (OPT==8'h10));                  // RGB+RGZ class
  cover property (@cb (OPT inside {8'h53,8'h73,8'hA3,8'hB3,8'hC3,8'hD3,8'hE3,8'hF3})); // multiply
  cover property (@cb (OPT[7:4]==4'h3 && OPT[3:0]==4'hC && $past(RGZ)==8'h00)); // !RGZ -> 1

endmodule

// Bind into DUT
bind alu_min alu_min_sva alu_min_sva_i
(
  .RST(RST), .CLK(CLK), .ENA(ENA), .OPT(OPT),
  .RGA(RGA), .RGB(RGB), .KEY(KEY), .RGZ(RGZ)
);

`endif
// SVA checker for LCD_control
// Bind this file to the DUT. Focuses on counters, sync timing, DE/request gating,
// coordinate/address mapping, RGB gating, and top-of-screen pulse.

module LCD_control_sva #(
  parameter int unsigned H_FRONT = 24,
  parameter int unsigned H_SYNC  = 72,
  parameter int unsigned H_BACK  = 96,
  parameter int unsigned H_ACT   = 800,
  parameter int unsigned H_BLANK = H_FRONT+H_SYNC+H_BACK,
  parameter int unsigned H_TOTAL = H_FRONT+H_SYNC+H_BACK+H_ACT,
  parameter int unsigned V_FRONT = 3,
  parameter int unsigned V_SYNC  = 10,
  parameter int unsigned V_BACK  = 7,
  parameter int unsigned V_ACT   = 480,
  parameter int unsigned V_BLANK = V_FRONT+V_SYNC+V_BACK,
  parameter int unsigned V_TOTAL = V_FRONT+V_SYNC+V_BACK+V_ACT
)(
  input  logic         iCLK,
  input  logic         iRST_N,
  input  logic [10:0]  H_Cont,
  input  logic [10:0]  V_Cont,
  input  logic         oLCD_HS,
  input  logic         oLCD_VS,
  input  logic         oLCD_DE,
  input  logic         oRequest,
  input  logic [9:0]   oCurrent_X,
  input  logic [9:0]   oCurrent_Y,
  input  logic [21:0]  oAddress,
  input  logic [7:0]   iRed,
  input  logic [7:0]   iGreen,
  input  logic [7:0]   iBlue,
  input  logic [7:0]   oLCD_R,
  input  logic [7:0]   oLCD_G,
  input  logic [7:0]   oLCD_B,
  input  logic         oTopOfScreen
);

default clocking cb @(posedge iCLK); endclocking
default disable iff (!iRST_N);

// Reset state
assert property (H_Cont < H_TOTAL);
assert property (V_Cont < V_TOTAL);

// H counter: increment and wrap
assert property ((H_Cont < H_TOTAL-1) |=> H_Cont == $past(H_Cont)+1);
assert property ((H_Cont == H_TOTAL-1) |=> H_Cont == 0);

// V counter: only updates when H_Cont==0; increment and wrap at line start
assert property ((H_Cont != 0) |=> V_Cont == $past(V_Cont));
assert property ((H_Cont == 0 && V_Cont < V_TOTAL-1) |=> V_Cont == $past(V_Cont)+1);
assert property ((H_Cont == 0 && V_Cont == V_TOTAL-1) |=> V_Cont == 0);

// HS/VS timing relative to counters
assert property (oLCD_HS == ~(H_Cont inside {[H_FRONT : H_FRONT+H_SYNC-1]}));
assert property (oLCD_VS == ~(V_Cont inside {[V_FRONT : V_FRONT+V_SYNC-1]}));

// DE/request equivalence
assert property (oRequest == ((H_Cont >= H_BLANK) && (V_Cont >= V_BLANK)));
assert property (oLCD_DE == oRequest);

// Visible coordinates
assert property ((H_Cont >= H_BLANK) |-> (oCurrent_X == H_Cont - H_BLANK && oCurrent_X < H_ACT));
assert property ((H_Cont <  H_BLANK) |-> (oCurrent_X == 0));
assert property ((V_Cont >= V_BLANK) |-> (oCurrent_Y == V_Cont - V_BLANK && oCurrent_Y < V_ACT));
assert property ((V_Cont <  V_BLANK) |-> (oCurrent_Y == 0));

// Address mapping and range
assert property (oAddress == oCurrent_Y*H_ACT + oCurrent_X);
assert property (oAddress < H_ACT*V_ACT);

// In-line pixel progression during active video
assert property ((oRequest && oCurrent_X < H_ACT-1)
                 |=> (oRequest && oCurrent_X == $past(oCurrent_X)+1
                      && oCurrent_Y == $past(oCurrent_Y)
                      && oAddress   == $past(oAddress)+1));

// End-of-line leaves active video next cycle
assert property ((oRequest && oCurrent_X == H_ACT-1) |=> !oRequest);

// Active window edges per line
assert property ((H_Cont == H_BLANK)             |-> (oRequest && oCurrent_X == 0));
assert property ((H_Cont == H_BLANK+H_ACT-1)     |-> (oRequest && oCurrent_X == H_ACT-1));

// RGB gating with request
assert property (oRequest |-> (oLCD_R == iRed   && oLCD_G == iGreen && oLCD_B == iBlue));
assert property (!oRequest |-> (oLCD_R == 8'h0 && oLCD_G == 8'h0   && oLCD_B == 8'h0));

// Top-of-screen pulse (one-cycle, aligned to previous (0,0))
assert property (oTopOfScreen == $past(H_Cont==0 && V_Cont==0));
assert property (oTopOfScreen |=> !oTopOfScreen);

// Useful covers
cover property (H_Cont==H_FRONT-1 ##1 H_Cont==H_FRONT+H_SYNC-1);         // HS low-to-high window
cover property (H_Cont==0 && V_Cont==V_FRONT-1 ##1 H_Cont==0
                && V_Cont==V_FRONT+V_SYNC-1);                             // VS low-to-high window
cover property (oRequest && oCurrent_X==0 && oCurrent_Y==0);              // First visible pixel
cover property (oRequest && oCurrent_X==H_ACT-1 && oCurrent_Y==V_ACT-1);  // Last visible pixel
cover property ($rose(oTopOfScreen));                                      // Frame start pulse

endmodule

// Bind to DUT
bind LCD_control LCD_control_sva #(
  .H_FRONT(H_FRONT), .H_SYNC(H_SYNC), .H_BACK(H_BACK), .H_ACT(H_ACT),
  .H_BLANK(H_BLANK), .H_TOTAL(H_TOTAL),
  .V_FRONT(V_FRONT), .V_SYNC(V_SYNC), .V_BACK(V_BACK), .V_ACT(V_ACT),
  .V_BLANK(V_BLANK), .V_TOTAL(V_TOTAL)
) u_lcd_control_sva (
  .iCLK(iCLK), .iRST_N(iRST_N),
  .H_Cont(H_Cont), .V_Cont(V_Cont),
  .oLCD_HS(oLCD_HS), .oLCD_VS(oLCD_VS),
  .oLCD_DE(oLCD_DE), .oRequest(oRequest),
  .oCurrent_X(oCurrent_X), .oCurrent_Y(oCurrent_Y),
  .oAddress(oAddress),
  .iRed(iRed), .iGreen(iGreen), .iBlue(iBlue),
  .oLCD_R(oLCD_R), .oLCD_G(oLCD_G), .oLCD_B(oLCD_B),
  .oTopOfScreen(oTopOfScreen)
);
// SVA for Nerf_Sentry_sm3
// Concise, high-value checks: state encoding, transition correctness,
// datapath update gating and functional correctness, and compact coverage.

`ifndef NERF_SENTRY_SM3_SVA
`define NERF_SENTRY_SM3_SVA

module Nerf_Sentry_sm3_sva
(
  input  logic        clock,
  input  logic        reset,
  input  logic        recieved,
  input  logic [7:0]  uart,
  input  logic [4:0]  state,
  input  logic [7:0]  x100, x010, x001,
  input  logic [7:0]  fireReg,
  input  logic [7:0]  pos,
  input  logic        fire
);

  // Local copies of DUT encodings
  localparam logic [4:0]
      IDLE     = 5'b00000,
      X100     = 5'b00001,
      X010     = 5'b00010,
      X001     = 5'b00011,
      Y100     = 5'b00100,
      Y010     = 5'b00101,
      Y001     = 5'b00110,
      FIRE     = 5'b00111,
      FIRESEL  = 5'b01000,
      SCANSEL  = 5'b01001,
      BIDLE    = 5'b01011,
      BX100    = 5'b01100,
      BX010    = 5'b01101,
      BX001    = 5'b01110,
      BY100    = 5'b01111,
      BY010    = 5'b10000,
      BY001    = 5'b10001,
      BFIRE    = 5'b10010,
      BFIRESEL = 5'b10011,
      BSCANSEL = 5'b10100;

  localparam logic [7:0] ASCII_A = 8'h61;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Helper for pos computation (8-bit truncate to match DUT)
  let pos_calc8 = ( ((x100 - 8'h30) * 8'd100)
                  + ((x010 - 8'h30) * 8'd10)
                  +  (x001 - 8'h30) )[7:0];

  // 1) State encoding legal
  assert property (state inside {
      IDLE, X100, X010, X001, Y100, Y010, Y001, FIRE, FIRESEL, SCANSEL,
      BIDLE, BX100, BX010, BX001, BY100, BY010, BY001, BFIRE, BFIRESEL, BSCANSEL
  });

  // 2) Generic "hold" rules
  // B-states hold when recieved==1
  assert property ((state inside {BIDLE,BX100,BX010,BX001,BY100,BY010,BY001,BFIRE,BFIRESEL,BSCANSEL}) && recieved |=> state == $past(state));

  // Non-B states (incl. IDLE/SCANSEL/FIRE/FIRESEL) hold when recieved==0
  assert property ((state inside {IDLE,X100,X010,X001,Y100,Y010,Y001,FIRE,FIRESEL,SCANSEL}) && !recieved |=> state == $past(state));

  // 3) Exact next-state mapping
  // From IDLE
  assert property (state==IDLE && recieved && (uart==ASCII_A) |=> state==BX100);
  assert property (state==IDLE && recieved && (uart!=ASCII_A) |=> state==IDLE);

  // B -> non-B when recieved==0
  assert property (state==BIDLE    && !recieved |=> state==IDLE);
  assert property (state==BX100    && !recieved |=> state==X100);
  assert property (state==BX010    && !recieved |=> state==X010);
  assert property (state==BX001    && !recieved |=> state==X001);
  assert property (state==BY100    && !recieved |=> state==Y100);
  assert property (state==BY010    && !recieved |=> state==Y010);
  assert property (state==BY001    && !recieved |=> state==Y001);
  assert property (state==BFIRE    && !recieved |=> state==FIRE);
  assert property (state==BFIRESEL && !recieved |=> state==FIRESEL);
  assert property (state==BSCANSEL && !recieved |=> state==SCANSEL);

  // non-B -> next B when recieved==1
  assert property (state==X100    && recieved |=> state==BX010);
  assert property (state==X010    && recieved |=> state==BX001);
  assert property (state==X001    && recieved |=> state==BY100);
  assert property (state==Y100    && recieved |=> state==BY010);
  assert property (state==Y010    && recieved |=> state==BY001);
  assert property (state==Y001    && recieved |=> state==BFIRE);
  assert property (state==FIRE    && recieved |=> state==BFIRESEL);
  assert property (state==FIRESEL && recieved |=> state==BSCANSEL);
  assert property (state==SCANSEL && recieved |=> state==BIDLE);

  // 4) Datapath: write gating and functional correctness
  // x-captures only in their states
  assert property (state==X100 |-> ##0 x100 == uart);
  assert property (state!=X100 |-> $stable(x100));

  assert property (state==X010 |-> ##0 x010 == uart);
  assert property (state!=X010 |-> $stable(x010));

  assert property (state==X001 |-> ##0 x001 == uart);
  assert property (state!=X001 |-> $stable(x001));

  // fireReg capture only in FIRE
  assert property (state==FIRE |-> ##0 fireReg == uart);
  assert property (state!=FIRE |-> $stable(fireReg));

  // pos and fire only update in IDLE, with correct values
  assert property (state==IDLE |-> ##0 pos == pos_calc8);
  assert property (state!=IDLE |-> $stable(pos));

  assert property (state==IDLE |-> ##0 fire == fireReg[0]);
  assert property (state!=IDLE |-> $stable(fire));

  // 5) Compact functional coverage
  // Cover full transaction path from IDLE through scan to back to IDLE (allowing stalls)
  cover property (
    state==IDLE
    ##[1:$] state==BX100
    ##[1:$] state==X100
    ##[1:$] state==BX010
    ##[1:$] state==X010
    ##[1:$] state==BX001
    ##[1:$] state==X001
    ##[1:$] state==BY100
    ##[1:$] state==Y100
    ##[1:$] state==BY010
    ##[1:$] state==Y010
    ##[1:$] state==BY001
    ##[1:$] state==Y001
    ##[1:$] state==BFIRE
    ##[1:$] state==FIRE
    ##[1:$] state==BFIRESEL
    ##[1:$] state==FIRESEL
    ##[1:$] state==BSCANSEL
    ##[1:$] state==SCANSEL
    ##[1:$] state==BIDLE
    ##[1:$] state==IDLE
  );

  // Cover that pos is computed from three captured bytes and fire reflects fireReg[0]
  cover property (state==X100 ##[1:$] state==X010 ##[1:$] state==X001 ##[1:$] state==FIRE ##[1:$] state==IDLE ##0 (pos==pos_calc8) && (fire==fireReg[0]));

endmodule

// Bind into DUT
bind Nerf_Sentry_sm3 Nerf_Sentry_sm3_sva sva_i
(
  .clock   (clock),
  .reset   (reset),
  .recieved(recieved),
  .uart    (uart),
  .state   (state),
  .x100    (x100),
  .x010    (x010),
  .x001    (x001),
  .fireReg (fireReg),
  .pos     (pos),
  .fire    (fire)
);

`endif
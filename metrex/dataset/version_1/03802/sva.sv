// SVA for uart51_tx
// Bind into DUT (assumes access to internal regs/wires)
bind uart51_tx uart51_tx_sva u_uart51_tx_sva (.*);

module uart51_tx_sva (
  input  BAUD_CLK,
  input  RESET_N,
  input  TX_DATA,
  input  TX_START,
  input  TX_DONE,
  input  TX_STOP,
  input  [1:0] TX_WORD,
  input  TX_PAR_DIS,
  input  [1:0] TX_PARITY,
  input  CTS,
  input  [7:0] TX_BUFFER,
  // internals
  input  [6:0] STATE,
  input  [2:0] BIT,
  input  TX_START0,
  input  TX_START1,
  input  PARITY
);

  // default clocking/reset
  default clocking cb @(negedge BAUD_CLK); endclocking
  default disable iff (!RESET_N);

  // State encodings of interest
  localparam [6:0] S_IDLE      = 7'b0000000;
  localparam [6:0] S_START     = 7'b0000001;
  localparam [6:0] S_DATA      = 7'b0010001;
  localparam [6:0] S_BIT_UPD   = 7'b0100000;
  localparam [6:0] S_PARITY    = 7'b0100001;
  localparam [6:0] S_STOP      = 7'b0110001;
  localparam [6:0] S_STOP_EDGE = 7'b0111111;
  localparam [6:0] S_CTS_CHK   = 7'b1001111;

  // Helper: explicit-state predicate
  function automatic bit is_explicit_state (logic [6:0] s);
    return (s==S_IDLE)      ||
           (s==S_START)     ||
           (s==S_DATA)      ||
           (s==S_BIT_UPD)   ||
           (s==S_PARITY)    ||
           (s==S_STOP)      ||
           (s==S_STOP_EDGE) ||
           (s==S_CTS_CHK);
  endfunction

  // Helper: recompute parity exactly as RTL
  function automatic logic parity_calc (
    input logic [7:0] b,
    input logic [1:0] w,
    input logic [1:0] p
  );
    parity_calc = (~p[1] &
                   ((b[0]^b[1])^(b[2]^b[3])) ^
                   (b[4] ^ (b[5] & (w != 2'b00))) ^
                   ((b[6] & (w[1]==1'b1)) ^ (b[7] & (w==2'b11)))
                  ) ^ ~p[0];
  endfunction

  // Reset values
  assert property (!RESET_N |-> (STATE==S_IDLE && TX_DATA==1'b1 && TX_DONE==1'b1 && BIT==3'b000 && TX_START0==1'b0 && TX_START1==1'b0));

  // No X on key signals
  assert property (!$isunknown({STATE,BIT,TX_DATA,TX_DONE})));

  // 2-flop synchronizer behavior
  assert property (TX_START0 == $past(TX_START));
  assert property (TX_START1 == $past(TX_START0));

  // Idle behavior
  assert property ((STATE==S_IDLE && !TX_START1) |=> STATE==S_IDLE);
  assert property (STATE==S_IDLE |-> TX_DATA==1'b1);
  assert property ((STATE==S_IDLE && TX_START1) |=> (STATE==S_START && TX_DONE==1'b0));

  // START state drives 0 and steps to +1
  assert property (STATE==S_START |-> TX_DATA==1'b0);
  assert property (STATE==S_START |=> STATE==7'b0000010);

  // Default states increment by +1
  assert property (!is_explicit_state(STATE) |=> STATE==$past(STATE)+7'd1);

  // DATA state drives correct data bit and steps to +1
  assert property (STATE==S_DATA |-> TX_DATA==TX_BUFFER[BIT]);
  assert property (STATE==S_DATA |=> STATE==7'b0010010);

  // BIT_UPD increments BIT
  assert property (STATE==S_BIT_UPD |=> BIT==$past(BIT)+3'd1);

  // BIT_UPD next-state decision per TX_WORD and TX_PAR_DIS (conditions use pre-increment BIT)
  assert property (
    STATE==S_BIT_UPD && ( (TX_WORD==2'b00 && $past(BIT)!=3'd7) ||
                          (TX_WORD==2'b01 && $past(BIT)!=3'd6) ||
                          (TX_WORD==2'b10 && $past(BIT)!=3'd5) ||
                          (TX_WORD==2'b11 && $past(BIT)!=3'd4) )
    |=> STATE==S_DATA
  );
  assert property (
    STATE==S_BIT_UPD &&
    !((TX_WORD==2'b00 && $past(BIT)!=3'd7) ||
      (TX_WORD==2'b01 && $past(BIT)!=3'd6) ||
      (TX_WORD==2'b10 && $past(BIT)!=3'd5) ||
      (TX_WORD==2'b11 && $past(BIT)!=3'd4))
    && !TX_PAR_DIS
    |=> STATE==S_PARITY
  );
  assert property (
    STATE==S_BIT_UPD &&
    !((TX_WORD==2'b00 && $past(BIT)!=3'd7) ||
      (TX_WORD==2'b01 && $past(BIT)!=3'd6) ||
      (TX_WORD==2'b10 && $past(BIT)!=3'd5) ||
      (TX_WORD==2'b11 && $past(BIT)!=3'd4))
    && TX_PAR_DIS
    |=> STATE==S_STOP
  );

  // Parity wire correctness and parity state behavior
  assert property (PARITY == parity_calc(TX_BUFFER, TX_WORD, TX_PARITY));
  assert property (STATE==S_PARITY |-> TX_DATA==PARITY);
  assert property (STATE==S_PARITY |=> STATE==7'b0100010);
  assert property (STATE==S_PARITY |-> $past(STATE)==S_BIT_UPD && !$past(TX_PAR_DIS));

  // Stop state drives done and 1, then advances
  assert property (STATE==S_STOP |-> (TX_DONE==1'b1 && TX_DATA==1'b1));
  assert property (STATE==S_STOP |=> STATE==7'b0110010);

  // End of first stop bit decision
  assert property (STATE==S_STOP_EDGE && !TX_STOP |=> STATE==S_CTS_CHK);
  assert property (STATE==S_STOP_EDGE &&  TX_STOP |=> STATE==7'b1000000);

  // CTS check behavior: wait while CTS==1, exit to idle when CTS==0
  assert property (STATE==S_CTS_CHK && CTS |=> STATE==S_CTS_CHK);
  assert property (STATE==S_CTS_CHK && !CTS |=> STATE==S_IDLE);

  // BIT only changes in IDLE reset or BIT_UPD
  assert property (!(STATE inside {S_BIT_UPD}) && !(STATE==S_IDLE) |=> BIT==$past(BIT));
  assert property (STATE==S_IDLE |-> BIT==3'd0);

  // TX_DATA stays high from STOP until next frame begins (no explicit re-drive until START)
  assert property (STATE==S_STOP ##1 1'b1 |-> TX_DATA throughout (! (STATE==S_START)));

  // Coverage: full-frame with parity disabled, 8/7/6/5-bit words
  cover property (STATE==S_IDLE && TX_START1 ##[1:$] STATE==S_STOP);
  cover property ($rose(TX_START1) && TX_WORD==2'b00 ##[1:$] $past(STATE)==S_BIT_UPD && $past(BIT)==3'd7 ##1 (STATE==S_PARITY || STATE==S_STOP));
  cover property ($rose(TX_START1) && TX_WORD==2'b01 ##[1:$] $past(STATE)==S_BIT_UPD && $past(BIT)==3'd6 ##1 (STATE==S_PARITY || STATE==S_STOP));
  cover property ($rose(TX_START1) && TX_WORD==2'b10 ##[1:$] $past(STATE)==S_BIT_UPD && $past(BIT)==3'd5 ##1 (STATE==S_PARITY || STATE==S_STOP));
  cover property ($rose(TX_START1) && TX_WORD==2'b11 ##[1:$] $past(STATE)==S_BIT_UPD && $past(BIT)==3'd4 ##1 (STATE==S_PARITY || STATE==S_STOP));

  // Coverage: parity enabled path, both parity values
  cover property (!TX_PAR_DIS ##[1:$] STATE==S_PARITY && PARITY==1'b0);
  cover property (!TX_PAR_DIS ##[1:$] STATE==S_PARITY && PARITY==1'b1);

  // Coverage: parity disabled direct-to-stop
  cover property ($past(STATE)==S_BIT_UPD && $past(TX_PAR_DIS) && STATE==S_STOP);

  // Coverage: TX_STOP=0, CTS holds high, then deasserts to exit
  cover property (STATE==S_STOP_EDGE && !TX_STOP ##1 STATE==S_CTS_CHK [*2:$] ##1 (!CTS) ##1 STATE==S_IDLE);

  // Coverage: TX_STOP=1 extra stop bit path reaches CTS_CHK then idle
  cover property (STATE==S_STOP_EDGE && TX_STOP ##[1:$] STATE==S_CTS_CHK ##[1:$] (!CTS) ##1 STATE==S_IDLE);

endmodule
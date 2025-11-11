// SVA for uart51_rx
// Bind these assertions to the DUT: bind uart51_rx uart51_rx_sva u_sva (.*);

module uart51_rx_sva
(
  input  logic        RESET_N,
  input  logic        BAUD_CLK,
  input  logic        RX_DATA,
  input  logic [7:0]  RX_BUFFER,
  input  logic [1:0]  RX_WORD,
  input  logic        RX_PAR_DIS,
  input  logic [1:0]  RX_PARITY,
  input  logic        PARITY_ERR,
  input  logic        FRAME,
  input  logic        READY,
  input  logic [5:0]  STATE,
  input  logic [2:0]  BIT,
  input  logic        RX_DATA0,
  input  logic        RX_DATA1
);

  // State encodings used in RTL
  localparam logic [5:0]
    S_IDLE        = 6'b000000,
    S_RDY_CLR     = 6'b001111,
    S_AFTER_CLR   = 6'b010000,
    S_SAMPLE      = 6'b010111,
    S_SAMPLE_NXT  = 6'b011000,
    S_BIT_DECIDE  = 6'b011111,
    S_PAR_SEL     = 6'b100000,
    S_PAR_EN_PATH = 6'b100001,
    S_PAR_CALC    = 6'b100111,
    S_AFTER_PARC  = 6'b101000,
    S_PAR_DIS_PATH= 6'b110001,
    S_STOP        = 6'b110111,
    S_WAIT_IDLE   = 6'b111000;

  // Helper predicates
  function automatic logic case_state(input logic [5:0] s);
    case_state = (s==S_IDLE) || (s==S_RDY_CLR) || (s==S_SAMPLE) || (s==S_BIT_DECIDE) ||
                 (s==S_PAR_SEL) || (s==S_PAR_CALC) || (s==S_STOP) || (s==S_WAIT_IDLE);
  endfunction

  function automatic logic bit_is_last(input logic [2:0] b, input logic [1:0] w);
    bit_is_last = (b==3'd7) ||
                  ((w==2'b01) && (b==3'd6)) ||
                  ((w==2'b10) && (b==3'd5)) ||
                  ((w==2'b11) && (b==3'd4));
  endfunction

  // Default clock/reset
  default clocking cb @(posedge BAUD_CLK); endclocking
  default disable iff (!RESET_N);

  // Reset values (async low)
  assert property ( !RESET_N |-> (STATE==S_IDLE && BIT==3'd0 && FRAME==1'b0 && READY==1'b0 &&
                                  RX_DATA0==1'b1 && RX_DATA1==1'b1 && RX_BUFFER==8'h00) );

  // Input two-flop synchronizer behavior
  assert property ( RX_DATA1 == $past(RX_DATA0) );
  assert property ( $past(RX_DATA0) == $past(RX_DATA) );

  // Idle behavior and start detection
  assert property ( (STATE==S_IDLE && RX_DATA1)  |=> (STATE==S_IDLE && BIT==3'd0) );
  assert property ( (STATE==S_IDLE && !RX_DATA1) |=> (STATE==6'b000001) );

  // Default increment in unspecified states
  assert property ( (!case_state(STATE)) |=> (STATE == $past(STATE)+6'd1) );

  // Ready deassert at S_RDY_CLR and next state
  assert property ( (STATE==S_RDY_CLR) |=> (STATE==S_AFTER_CLR && READY==1'b0) );

  // Timings between key states
  assert property ( (STATE==6'b000001)  |-> ##14 (STATE==S_RDY_CLR) );     // 000001 -> 001111
  assert property ( (STATE==S_AFTER_CLR)|-> ##7  (STATE==S_SAMPLE) );      // 010000 -> 010111
  assert property ( (STATE==S_SAMPLE)   |=>      (STATE==S_SAMPLE_NXT) );  // 010111 -> 011000
  assert property ( (STATE==S_SAMPLE_NXT)|-> ##7 (STATE==S_BIT_DECIDE) );  // 011000 -> 011111

  // Bit sampling correctness (sampled bit captured into buffer)
  assert property ( (STATE==S_SAMPLE) |=> (RX_BUFFER[$past(BIT)] == $past(RX_DATA1)) );

  // Bit-loop decision
  assert property ( (STATE==S_BIT_DECIDE && !bit_is_last(BIT,RX_WORD))
                    |=> (STATE==S_AFTER_CLR && BIT==$past(BIT)+3'd1) );
  assert property ( (STATE==S_BIT_DECIDE &&  bit_is_last(BIT,RX_WORD))
                    |=> (STATE==S_PAR_SEL && BIT==$past(BIT)) );

  // Parity path select
  assert property ( (STATE==S_PAR_SEL &&  RX_PAR_DIS) |=> (STATE==S_PAR_DIS_PATH) );
  assert property ( (STATE==S_PAR_SEL && !RX_PAR_DIS) |=> (STATE==S_PAR_EN_PATH) );

  // Parity disabled timing to STOP
  assert property ( (STATE==S_PAR_DIS_PATH) |-> ##6 (STATE==S_STOP) );

  // Parity enabled timing and calculation
  assert property ( (STATE==S_PAR_EN_PATH) |-> ##6 (STATE==S_PAR_CALC) );
  assert property ( (STATE==S_PAR_CALC)    |=>      (STATE==S_AFTER_PARC) );
  assert property ( (STATE==S_AFTER_PARC)  |-> ##15 (STATE==S_STOP) );

  // Parity error register update at S_PAR_CALC
  // Note: mirrors RTL formula intentionally
  assert property ( (STATE==S_PAR_CALC)
                    |=> ( PARITY_ERR ==
                          ( ~$past(RX_PARITY[1]) &
                            ( (^$past(RX_BUFFER)) ^ ((~$past(RX_PARITY[0])) ^ $past(RX_DATA1)) )
                          )
                        )
                  );

  // STOP: framing check and READY assert
  assert property ( (STATE==S_STOP) |=> (READY==1'b1 && FRAME == !$past(RX_DATA1)) );

  // WAIT_IDLE: hold until stop bit high, then go idle
  assert property ( (STATE==S_WAIT_IDLE &&  RX_DATA1) |=> (STATE==S_IDLE) );
  assert property ( (STATE==S_WAIT_IDLE && !RX_DATA1) |=> (STATE==S_WAIT_IDLE) );

  // READY stays high until explicitly cleared at S_RDY_CLR
  assert property ( $rose(READY) |-> ( READY until_with (STATE==S_RDY_CLR) ) );

  // ---------------------------------
  // Coverage (concise but complete)
  // ---------------------------------
  // Cover a complete frame without parity
  cover property ( (STATE==S_IDLE && !RX_DATA1 && RX_PAR_DIS)
                   ##[1:$] (STATE==S_STOP && READY==1) );

  // Cover a complete frame with parity enabled
  cover property ( (STATE==S_IDLE && !RX_DATA1 && !RX_PAR_DIS)
                   ##[1:$] (STATE==S_PAR_CALC)
                   ##[1:$] (STATE==S_STOP && READY==1) );

  // Cover parity error observed
  cover property ( (STATE==S_PAR_CALC) ##1 (PARITY_ERR==1'b1) );

  // Cover framing error observed at STOP
  cover property ( (STATE==S_STOP && FRAME==1'b1) );

  // Cover each word length termination at S_BIT_DECIDE
  cover property ( (STATE==S_BIT_DECIDE && RX_WORD==2'b00 && BIT==3'd7) );
  cover property ( (STATE==S_BIT_DECIDE && RX_WORD==2'b01 && BIT==3'd6) );
  cover property ( (STATE==S_BIT_DECIDE && RX_WORD==2'b10 && BIT==3'd5) );
  cover property ( (STATE==S_BIT_DECIDE && RX_WORD==2'b11 && BIT==3'd4) );

endmodule
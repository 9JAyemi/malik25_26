// SVA for message_formatter
// Bind this file to the DUT: bind message_formatter message_formatter_sva #(.WIDTH(WIDTH),.COUNT(COUNT),.TX_INTERVAL(TX_INTERVAL)) u_sva (.*);

module message_formatter_sva #(
  parameter int WIDTH       = 24,
  parameter int COUNT       = 2,
  parameter int TX_INTERVAL = 4
)(
  input  logic                       CLK,
  input  logic                       RST,

  // DUT ports
  input  logic                       I_STB,
  input  logic [(WIDTH*COUNT)-1:0]   I_DAT,
  input  logic                       O_STB,
  input  logic [7:0]                 O_DAT,

  // DUT internals (bind to these)
  input  logic [24:0]                tx_dly_cnt,
  input  logic                       tx_req,
  input  logic                       tx_rdy,
  input  logic [7:0]                 char_cnt,
  input  logic [7:0]                 word_cnt,
  input  logic [(WIDTH*COUNT)-1:0]   sr_reg,
  input  logic [3:0]                 sr_dat,
  input  integer                     fsm,
  input  logic                       o_stb,
  input  logic [7:0]                 o_dat
);

  localparam int TOTAL_WIDTH = WIDTH*COUNT;

  // FSM encodings (must match DUT)
  localparam int FSM_IDLE   = 'h00;
  localparam int FSM_TX_HEX = 'h11;
  localparam int FSM_TX_CR  = 'h21;
  localparam int FSM_TX_LF  = 'h22;
  localparam int FSM_TX_SEP = 'h31;

  // Clocking
  default clocking cb @(posedge CLK); endclocking

  // Helper
  function automatic [7:0] ascii_hex(input logic [3:0] n);
    ascii_hex = (n < 10) ? (8'h30 + n) : (8'h41 + (n-10)); // "0"-"9","A"-"F"
  endfunction

  // 1) Basic signal/port consistency
  assert property (disable iff (RST) O_STB == o_stb);
  assert property (disable iff (RST) O_DAT == o_dat);

  // 2) FSM legal state
  assert property (disable iff (RST)
    fsm inside {FSM_IDLE, FSM_TX_HEX, FSM_TX_SEP, FSM_TX_CR, FSM_TX_LF}
  );

  // 3) tx_req reflects TX states (registered off previous cycle FSM)
  assert property (disable iff (RST)
    tx_req == ($past(fsm) inside {FSM_TX_HEX, FSM_TX_SEP, FSM_TX_CR, FSM_TX_LF})
  );

  // 4) o_stb is the registered handshake
  assert property (disable iff (RST) o_stb == $past(tx_req & tx_rdy));
  assert property (disable iff (RST) o_stb |-> $past(fsm) inside {FSM_TX_HEX,FSM_TX_SEP,FSM_TX_CR,FSM_TX_LF});

  // 5) tx interval behavior
  // Load on handshake
  assert property (disable iff (RST)
    $past(tx_rdy && tx_req) |=> tx_dly_cnt == (TX_INTERVAL-2)
  );
  // Decrement while not ready
  assert property (disable iff (RST)
    $past(!tx_rdy) |=> tx_dly_cnt == $past(tx_dly_cnt) - 1
  );
  // After any handshake, tx_rdy stays low for TX_INTERVAL-1 cycles then returns high
  assert property (disable iff (RST)
    (tx_req && tx_rdy)
      |=> (!tx_rdy)[* (TX_INTERVAL-1)] ##1 tx_rdy
  );

  // 6) char_cnt behavior
  localparam int NYBS_PER_WORD = (WIDTH/4);
  assert property (disable iff (RST)
    $past(fsm inside {FSM_IDLE, FSM_TX_SEP}) |=> char_cnt == (NYBS_PER_WORD-1)
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_HEX && tx_rdy) |=> char_cnt == $past(char_cnt) - 1
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_HEX && !tx_rdy) |=> char_cnt == $past(char_cnt)
  );

  // 7) word_cnt behavior
  assert property (disable iff (RST)
    $past(fsm==FSM_IDLE) |=> word_cnt == (COUNT-1)
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_SEP && tx_rdy) |=> word_cnt == $past(word_cnt) - 1
  );
  assert property (disable iff (RST)
    $past(!(fsm==FSM_IDLE) && !(fsm==FSM_TX_SEP && tx_rdy)) |=> word_cnt == $past(word_cnt)
  );

  // 8) Shift register behavior
  assert property (disable iff (RST)
    $past(fsm==FSM_IDLE && I_STB) |=> sr_reg == $past(I_DAT)
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_HEX && tx_rdy) |=> sr_reg == ($past(sr_reg) << 4)
  );
  assert property (disable iff (RST)
    $past(!(fsm==FSM_IDLE && I_STB) && !(fsm==FSM_TX_HEX && tx_rdy)) |=> sr_reg == $past(sr_reg)
  );

  // 9) FSM transitions
  assert property (disable iff (RST)
    $past(fsm==FSM_IDLE && I_STB) |=> fsm==FSM_TX_HEX
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_HEX && tx_rdy && (char_cnt!=0)) |=> fsm==FSM_TX_HEX
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_HEX && tx_rdy && (char_cnt==0) && (word_cnt!=0)) |=> fsm==FSM_TX_SEP
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_HEX && tx_rdy && (char_cnt==0) && (word_cnt==0)) |=> fsm==FSM_TX_CR
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_SEP && tx_rdy) |=> fsm==FSM_TX_HEX
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_CR && tx_rdy) |=> fsm==FSM_TX_LF
  );
  assert property (disable iff (RST)
    $past(fsm==FSM_TX_LF && tx_rdy) |=> fsm==FSM_IDLE
  );

  // 10) Output data correctness on valid strobe (note: o_stb is 1-cycle after tx_req&tx_rdy)
  // CR/LF/SEP literals
  assert property (disable iff (RST)
    o_stb && $past(fsm)==FSM_TX_CR |-> O_DAT == 8'h0D
  );
  assert property (disable iff (RST)
    o_stb && $past(fsm)==FSM_TX_LF |-> O_DAT == 8'h0A
  );
  assert property (disable iff (RST)
    o_stb && $past(fsm)==FSM_TX_SEP |-> O_DAT == 8'h5F // "_"
  );
  // HEX encoding
  assert property (disable iff (RST)
    o_stb && $past(fsm)==FSM_TX_HEX |-> O_DAT == ascii_hex($past(sr_dat))
  );

  // 11) Liveness: a started frame completes (returns to IDLE via CR/LF)
  assert property (disable iff (RST)
    (fsm==FSM_IDLE && I_STB)
      |=> ##[1:$] (o_stb && $past(fsm)==FSM_TX_CR)
       ##[1:$] (o_stb && $past(fsm)==FSM_TX_LF)
       ##[1:$] (fsm==FSM_IDLE)
  );

  // 12) Coverage
  // See all TX states at least once
  cover property (disable iff (RST) (fsm==FSM_TX_HEX));
  if (COUNT>1) cover property (disable iff (RST) (o_stb && $past(fsm)==FSM_TX_SEP));
  cover property (disable iff (RST) (o_stb && $past(fsm)==FSM_TX_CR));
  cover property (disable iff (RST) (o_stb && $past(fsm)==FSM_TX_LF));
  // See a full transaction: start, SEP (if COUNT>1), CR, LF, back to IDLE
  if (COUNT>1)
    cover property (disable iff (RST)
      (fsm==FSM_IDLE && I_STB)
        ##[1:$] (o_stb && $past(fsm)==FSM_TX_SEP)
        ##[1:$] (o_stb && $past(fsm)==FSM_TX_CR)
        ##[1:$] (o_stb && $past(fsm)==FSM_TX_LF)
        ##[1:$] (fsm==FSM_IDLE)
    );
  else
    cover property (disable iff (RST)
      (fsm==FSM_IDLE && I_STB)
        ##[1:$] (o_stb && $past(fsm)==FSM_TX_CR)
        ##[1:$] (o_stb && $past(fsm)==FSM_TX_LF)
        ##[1:$] (fsm==FSM_IDLE)
    );
  // Exercise a couple of HEX digits
  cover property (disable iff (RST) o_stb && $past(fsm)==FSM_TX_HEX && O_DAT==8'h30); // "0"
  cover property (disable iff (RST) o_stb && $past(fsm)==FSM_TX_HEX && O_DAT==8'h46); // "F"

endmodule
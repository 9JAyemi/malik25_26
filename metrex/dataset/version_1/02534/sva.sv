// SVA for crc_16. Bind this file to the DUT.
// Focused, high-signal-coverage checks of FSM, counters, data path, and done pulse.

module crc_16_sva;
  // Mirror DUT params/constants
  localparam int DATAWIDTH = 32;
  localparam int CRCORDER  = 16;
  localparam [CRCORDER:0] POLY = 17'b10001000000100001;

  // FSM encodings
  localparam [2:0] INIT=3'd0, GET=3'd1, COMP=3'd2, XOR=3'd3, CORRER=3'd4, SEND=3'd5;

  default clocking cb @(posedge clk); endclocking

  // Reset effect (synchronous)
  assert property (rst |=> state==INIT && cont==0 && proceso=='0 && rdone==0);

  // Legal/known state encodings
  assert property (disable iff (rst) !$isunknown(state) && (state inside {INIT,GET,COMP,XOR,CORRER,SEND}));

  // Output wiring
  assert property (disable iff (rst) done == rdone);
  assert property (disable iff (rst) data_out == proceso[15:0]);

  // INIT transitions and effects
  assert property (disable iff (rst) state==INIT && !start |-> ##1 state==INIT && cont==0 && rdone==0);
  assert property (disable iff (rst) state==INIT &&  start |-> ##1 state==GET && r_data == $past(data_in));

  // GET: load window from r_data, then go to COMP
  assert property (disable iff (rst) state==GET |-> ##1 state==COMP && proceso == $past(r_data[31:31-CRCORDER]));

  // COMP: increment counter, branch on MSB of proceso
  assert property (disable iff (rst) state==COMP |-> ##1 cont == $past(cont)+1);
  assert property (disable iff (rst) state==COMP &&  proceso[CRCORDER] |-> ##1 state==XOR);
  assert property (disable iff (rst) state==COMP && !proceso[CRCORDER] |-> ##1 state==CORRER);

  // XOR: apply polynomial, then CORRER
  assert property (disable iff (rst) state==XOR |-> ##1 state==CORRER && proceso == ($past(proceso) ^ POLY));

  // CORRER: branch on cont, enforce LSB shift-in = 0
  assert property (disable iff (rst) state==CORRER && cont != DATAWIDTH |-> ##1 state==GET);
  assert property (disable iff (rst) state==CORRER && cont == DATAWIDTH |-> ##1 state==SEND);
  assert property (disable iff (rst) state==CORRER |-> ##1 r_data[0] == 1'b0);

  // SEND: done pulse and return to INIT
  assert property (disable iff (rst) state==SEND |-> ##1 (state==INIT && done));
  assert property (disable iff (rst) done |-> $past(state)==SEND && state==INIT);
  assert property (disable iff (rst) done |-> ##1 !done);
  assert property (disable iff (rst) done |-> cont == DATAWIDTH);

  // Outputs not X/Z after reset
  assert property (disable iff (rst) !$isunknown({done, data_out}));

  // Progress/liveness: a taken start leads to done within a bound
  assert property (disable iff (rst) state==INIT && start |-> ##[1:200] done);

  // Coverage
  cover property (disable iff (rst) state==INIT && start ##1 state==GET ##1 state==COMP ##[1:$] state==SEND ##1 !done);
  cover property (disable iff (rst) state==COMP &&  proceso[CRCORDER] ##1 state==XOR);
  cover property (disable iff (rst) state==COMP && !proceso[CRCORDER] ##1 state==CORRER);
  cover property (disable iff (rst) state==CORRER && cont == DATAWIDTH ##1 state==SEND);
endmodule

bind crc_16 crc_16_sva sva();
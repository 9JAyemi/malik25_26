// SVA for UART_TX
// Bind this module to the DUT: 
//   bind UART_TX UART_TX_assertions u_uart_tx_assertions (.*);

module UART_TX_assertions (
  input  logic        rst, clk, baud_edge, data_ready,
  input  logic [7:0]  data,
  input  logic        tx, data_accepted,
  input  logic [7:0]  data_reg,
  input  logic [2:0]  data_counter,
  input  logic [3:0]  state
);

  localparam logic [3:0] START = 4'd1;
  localparam logic [3:0] DATA  = 4'd2;
  localparam logic [3:0] END   = 4'd4;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helper: the very next baud_edge must satisfy expr (cannot skip a baud_edge)
  sequence NB(logic expr);
    (!baud_edge)[*0:$] ##1 (baud_edge && expr);
  endsequence

  // Reset effects
  assert property (@(posedge clk) rst |=> (state==END && tx==1 && data_accepted==0));

  // State encoding valid
  assert property (state inside {START, DATA, END});

  // No state/tx/counter changes without baud_edge
  assert property (!baud_edge |-> $stable(state) && $stable(tx) && $stable(data_counter));

  // data_accepted behavior
  assert property (!baud_edge |-> !data_accepted);
  assert property (baud_edge && data_accepted |-> (state==END && data_ready));
  assert property (baud_edge && !(state==END && data_ready) |-> !data_accepted);

  // Idle/stop-bit high whenever in END at baud_edge
  assert property (baud_edge && state==END |-> tx==1);

  // START cycle behavior and transition
  assert property (baud_edge && state==START |-> (tx==0 && data_counter==0));
  assert property (baud_edge && state==START |-> NB(state==DATA && data_counter==0));

  // DATA phase: bit correctness and counter progress
  assert property (baud_edge && state==DATA |-> tx == data_reg[data_counter]);

  // Counter increments within DATA
  assert property (
    (baud_edge && state==DATA && data_counter!=3'd7, automatic logic [2:0] c = data_counter)
      |-> NB(state==DATA && data_counter==c+3'd1)
  );

  // Wrap to END after last data bit
  assert property (baud_edge && state==DATA && data_counter==3'd7 |-> NB(state==END && data_counter==3'd0));

  // Accept handshake latches data_reg and leads to START on next baud_edge
  assert property (
    (baud_edge && state==END && data_ready, automatic logic [7:0] cap = data)
      |=> (data_reg == cap)
  );
  assert property (baud_edge && state==END && data_ready |-> NB(state==START && tx==0 && data_counter==0));

  // Illegal state self-recovers to END on next cycle (via default)
  assert property (baud_edge && !(state inside {START,DATA,END}) |=> state==END);

  // Optional X-checks
  assert property (!$isunknown(tx));
  assert property (!$isunknown(state));

  // COVERAGE: one full frame (accept -> start -> 8 data bits -> stop)
  cover property (
    (baud_edge && state==END && data_ready)
      ##0 NB(state==START)
      ##0 NB(state==DATA && data_counter==3'd0)
      ##0 NB(state==DATA && data_counter==3'd1)
      ##0 NB(state==DATA && data_counter==3'd2)
      ##0 NB(state==DATA && data_counter==3'd3)
      ##0 NB(state==DATA && data_counter==3'd4)
      ##0 NB(state==DATA && data_counter==3'd5)
      ##0 NB(state==DATA && data_counter==3'd6)
      ##0 NB(state==DATA && data_counter==3'd7)
      ##0 NB(state==END)
  );

endmodule

// Example bind (place in a separate file or a package imported by the testbench)
// bind UART_TX UART_TX_assertions u_uart_tx_assertions (.*);
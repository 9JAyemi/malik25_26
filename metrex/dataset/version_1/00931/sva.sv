// Bindable SVA for uart
module uart_sva
  #(parameter int DATA_BITS = 8,
    parameter int BAUD      = 19200,
    parameter int CLK_RATE  = 100000000)
  (
    input  logic                  clk,
    input  logic                  rst,
    input  logic                  rx,
    input  logic                  busy,
    input  logic [7:0]            data,
    input  logic [1:0]            state,
    input  logic                  rx_reg,
    input  logic [$clog2(CLK_DIV)-1:0]        baud_counter,
    input  logic [$clog2(DATA_BITS)-1:0]      rx_counter
  );

  localparam int CLK_DIV = CLK_RATE/BAUD;
  localparam logic [1:0] STATE_IDLE = 2'b00;
  localparam logic [1:0] STATE_WAIT = 2'b01;
  localparam logic [1:0] STATE_RX   = 2'b10;
  localparam logic [1:0] STATE_END  = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset effect (synchronous)
  assert property (@(posedge clk) rst |-> (state==STATE_IDLE && busy==1'b0 && data==8'h00));

  // No X/Z on key signals when not in reset
  assert property (!$isunknown({state,busy,rx_reg,baud_counter,rx_counter,data})));

  // State encoding only
  assert property (state inside {STATE_IDLE,STATE_WAIT,STATE_RX,STATE_END});

  // Busy relationship with state
  assert property ((state==STATE_IDLE) |-> !busy);
  assert property ((state!=STATE_IDLE) |->  busy);

  // Busy edges are legal
  assert property ($rose(busy) |-> $past(state==STATE_IDLE && !rx_reg));
  assert property ($fell(busy) |-> $past(state==STATE_END && baud_counter==CLK_DIV-1 && rx_reg));

  // Idle -> WaitHalf on start bit; counters cleared, busy set
  assert property ((state==STATE_IDLE && !rx_reg)
                   |=> (state==STATE_WAIT && busy && rx_counter==0 && baud_counter==0));

  // WaitHalf counting behavior
  assert property ((state==STATE_WAIT && baud_counter != (CLK_DIV/2)-1)
                   |=> (state==STATE_WAIT && baud_counter == $past(baud_counter)+1));
  assert property ((state==STATE_WAIT && baud_counter == (CLK_DIV/2)-1)
                   |=> (state==STATE_RX && baud_counter==0));

  // RX counting and sampling behavior
  assert property ((state==STATE_RX && baud_counter != CLK_DIV-1)
                   |=> (state==STATE_RX && baud_counter==$past(baud_counter)+1 && rx_counter==$past(rx_counter)));
  // Sample bit (not last)
  assert property ((state==STATE_RX && baud_counter==CLK_DIV-1 && rx_counter!=DATA_BITS-1)
                   |=> (state==STATE_RX && baud_counter==0 &&
                        rx_counter==$past(rx_counter)+1 &&
                        data == { $past(rx_reg), $past(data)[7:1] }));
  // Sample last bit -> END
  assert property ((state==STATE_RX && baud_counter==CLK_DIV-1 && rx_counter==DATA_BITS-1)
                   |=> (state==STATE_END && baud_counter==0 &&
                        data == { $past(rx_reg), $past(data)[7:1] }));

  // END state timing and stop-bit check
  assert property ((state==STATE_END && baud_counter != CLK_DIV-1)
                   |=> (state==STATE_END && baud_counter==$past(baud_counter)+1));
  assert property ((state==STATE_END && baud_counter==CLK_DIV-1 &&  rx_reg)
                   |=> (state==STATE_IDLE && !busy && baud_counter==0));
  assert property ((state==STATE_END && baud_counter==CLK_DIV-1 && !rx_reg)
                   |=> (state==STATE_END && busy && baud_counter==0));

  // Data can only change on RX sample ticks
  assert property (! (state==STATE_RX && baud_counter==CLK_DIV-1)
                   |=> data == $past(data));

  // Counter ranges
  assert property (rx_counter < DATA_BITS);
  assert property ((state inside {STATE_WAIT,STATE_RX,STATE_END}) |-> (baud_counter < CLK_DIV));

  // Coverage: complete good frame (start -> RX bits -> stop -> idle)
  cover property ($rose(busy)
                  ##[1:$] (state==STATE_RX && rx_counter==DATA_BITS-1 && baud_counter==CLK_DIV-1)
                  ##1 (state==STATE_END)
                  ##[1:$] ($fell(busy) && state==STATE_IDLE));

  // Coverage: bad stop bit causes extension of END before returning to IDLE
  cover property ((state==STATE_END && baud_counter==CLK_DIV-1 && !rx_reg)
                  ##1 state==STATE_END
                  ##[1:$] (state==STATE_END && baud_counter==CLK_DIV-1 && rx_reg)
                  ##1 (state==STATE_IDLE && !busy));

endmodule

// Bind into DUT (tools typically allow binding to internal regs via matching port names)
bind uart uart_sva #(.DATA_BITS(DATA_BITS), .BAUD(BAUD), .CLK_RATE(CLK_RATE)) u_uart_sva (.*);
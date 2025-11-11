// SVA for uart_tx
// Bind this file to the DUT:
//   bind uart_tx uart_tx_sva #(.DATA_WIDTH(DATA_WIDTH)) i_uart_tx_sva();

module uart_tx_sva #(parameter DATA_WIDTH=8) ();

  // Use DUT scope signals (this module is bound into uart_tx)
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // -------------------------
  // Basic reset and no-X checks
  // -------------------------
  assert property (rst |-> ##1 (input_axis_tready==0 && txd==1 && busy==0 && prescale_reg==0 && bit_cnt==0));
  assert property (!$isunknown({txd,busy,input_axis_tready}));

  // -------------------------
  // Ready/Busy protocol
  // -------------------------
  // Ready only when fully idle
  assert property (input_axis_tready |-> (prescale_reg==0 && bit_cnt==0 && !busy));
  // Any activity forces not ready
  assert property ((prescale_reg>0 || bit_cnt>0) |-> !input_axis_tready);
  // Busy implies activity; idle implies not busy
  assert property (busy |-> (prescale_reg>0 || bit_cnt>0));
  assert property ((prescale_reg==0 && bit_cnt==0) |-> !busy);
  // Busy edges
  assert property ($rose(busy) |-> $past(input_axis_tvalid && input_axis_tready));
  assert property ($fell(busy) |-> (input_axis_tready && prescale_reg==0 && bit_cnt==0 && txd==1));

  // -------------------------
  // Handshake and load behavior
  // -------------------------
  // Accepting a word launches a frame: start bit, counters/prescale load, not-ready, busy set
  assert property (
    (input_axis_tvalid && input_axis_tready)
    |=> (txd==0 && busy && !input_axis_tready
         && bit_cnt == (uart_data_width + ((uart_stopbit!=2'b00) ? 2 : 1))
         && prescale_reg == ((prescale<<3) - 1))
  );

  // -------------------------
  // Prescale countdown and stability between bit boundaries
  // -------------------------
  // When prescale_reg was >0, it must decrement and outputs hold (no ready)
  assert property (($past(prescale_reg>0)) |-> (prescale_reg == $past(prescale_reg)-1 && !input_axis_tready && txd==$past(txd)));

  // -------------------------
  // Bit shifting and timing reloads
  // -------------------------
  // Regular shift step (from prev cycle) when more than one bit left
  assert property (
    $past(prescale_reg==0 && bit_cnt>1)
    |-> ( txd == $past(data_reg[0])
          && data_reg == {1'b0, $past(data_reg[DATA_WIDTH+2:1])}
          && bit_cnt == $past(bit_cnt)-1
          && prescale_reg == ((($past(bit_cnt)==2) && $past(uart_stopbit[1])) ? ((prescale<<2)-1) : ((prescale<<3)-1))
        )
  );

  // Last data/stop transition step
  assert property (
    $past(prescale_reg==0 && bit_cnt==1)
    |-> (txd==1 && bit_cnt==0 && prescale_reg==(prescale<<3))
  );

  // Line idle is high whenever not sending any bit (bit_cnt==0 at this edge)
  assert property ((bit_cnt==0) |-> txd==1);

  // -------------------------
  // Data register load content (no parity vs with parity)
  // -------------------------
  // No parity case
  assert property (
    (input_axis_tvalid && input_axis_tready && uart_parity==2'b00)
    |=> (
          (uart_bits==2'b00 && data_reg == {3'b111,   input_axis_tdata}) ||
          (uart_bits==2'b01 && data_reg == {4'b1111,  input_axis_tdata[DATA_WIDTH-2:0]}) ||
          (uart_bits==2'b10 && data_reg == {5'b11111, input_axis_tdata[DATA_WIDTH-3:0]}) ||
          (uart_bits==2'b11 && data_reg == {6'b111111,input_axis_tdata[DATA_WIDTH-4:0]})
        )
  );

  // Parity present case
  assert property (
    (input_axis_tvalid && input_axis_tready && uart_parity!=2'b00)
    |=> (
          (uart_bits==2'b00 && data_reg == {2'b11,    parity, input_axis_tdata}) ||
          (uart_bits==2'b01 && data_reg == {3'b111,   parity, input_axis_tdata[DATA_WIDTH-2:0]}) ||
          (uart_bits==2'b10 && data_reg == {4'b1111,  parity, input_axis_tdata[DATA_WIDTH-3:0]}) ||
          (uart_bits==2'b11 && data_reg == {5'b11111, parity, input_axis_tdata[DATA_WIDTH-4:0]})
        )
  );

  // Parity definition (sanity, mirrors RTL)
  assert property (parity == (^(input_axis_tdata & bitmask_parity_reversed)) ^ uart_parity[1]);

  // -------------------------
  // Config stability while busy (recommendation)
  // -------------------------
  assert property (busy |-> $stable({uart_bits, uart_parity, uart_stopbit, uart_data_width, prescale}));

  // -------------------------
  // Environment assumptions (AXI-stream like)
  // -------------------------
  // Hold tdata stable while waiting; keep tvalid asserted until ready
  assume property ((input_axis_tvalid && !input_axis_tready) |-> (input_axis_tvalid && $stable(input_axis_tdata)));

  // -------------------------
  // Coverage
  // -------------------------
  // Any valid handshake
  cover property (input_axis_tvalid && input_axis_tready);
  // Parity off/on
  cover property (input_axis_tvalid && input_axis_tready && uart_parity==2'b00);
  cover property (input_axis_tvalid && input_axis_tready && uart_parity!=2'b00);
  // All data width select values
  cover property (input_axis_tvalid && input_axis_tready && uart_bits==2'b00);
  cover property (input_axis_tvalid && input_axis_tready && uart_bits==2'b01);
  cover property (input_axis_tvalid && input_axis_tready && uart_bits==2'b10);
  cover property (input_axis_tvalid && input_axis_tready && uart_bits==2'b11);
  // Two-stop-bit path taken (special prescale for second stop bit)
  cover property ($past(prescale_reg==0 && bit_cnt==2) && uart_stopbit[1] && prescale_reg == ((prescale<<2)-1));
  // Back-to-back frames
  cover property ((input_axis_tvalid && input_axis_tready) ##[1:$] (input_axis_tvalid && input_axis_tready));
  // Prescale extremes
  cover property (input_axis_tvalid && input_axis_tready && prescale==16'd1);
  cover property (input_axis_tvalid && input_axis_tready && prescale>16'd1);

endmodule

// Bind into DUT
bind uart_tx uart_tx_sva #(.DATA_WIDTH(DATA_WIDTH)) i_uart_tx_sva();
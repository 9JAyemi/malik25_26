// SystemVerilog Assertions for baudgen, uart, rxuart, buart
// Bind these into the DUT; concise but high-quality checks and covers

// ---------------- baudgen ----------------
bind baudgen baudgen_sva();
module baudgen_sva;
  localparam int W = $bits(d);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetq);

  // Structural/behavioral correctness
  assert property (ser_clk == ~d[W-1]);

  // Next-state function
  assert property (d == ($past(restart) ? '0 : ($past(d) + $past(dInc))));

  // Restart zeroes accumulator next cycle
  assert property (restart |=> d == '0);

  // Reset drives accumulator idle and ser_clk high on next clk
  assert property (@(posedge clk) !resetq |-> (d == '0 && ser_clk == 1'b1));

  // Exercise both accumulator MSB regions (forces both dInc branches)
  cover property (d[W-1] ##1 !d[W-1]);
  cover property ($rose(ser_clk));
  cover property ($fell(ser_clk));
endmodule


// ---------------- uart (TX) ----------------
bind uart uart_sva();
module uart_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetq);

  // Busy definition matches bitcount
  assert property (uart_busy == (bitcount != 0));

  // TX idles high when not sending
  assert property (!(|bitcount) |-> uart_tx == 1'b1);

  // Starting loads shifter and bitcount (start + 8 data + stop = 10)
  assert property (starting |=> (shifter == {uart_dat_i, 1'b0} && bitcount == 10));

  // Each baud tick while sending: shift and decrement
  assert property ((|bitcount) && ser_clk |=> 
                   (bitcount == $past(bitcount) - 1) &&
                   ({shifter, uart_tx} == {1'b1, $past(shifter)}));

  // Bitcount stable otherwise
  assert property (!(starting || ((|bitcount) && ser_clk)) |=> bitcount == $past(bitcount));

  // Full TX transaction coverage: accept start, shift 10 bits, return idle
  cover property (starting ##1 ((|bitcount) && ser_clk)[*10] ##1 !(|bitcount));
endmodule


// ---------------- rxuart (RX) ----------------
bind rxuart rxuart_sva();
module rxuart_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetq);

  // Definitions
  assert property (idle == &bitcount);
  assert property (valid == (bitcount == 5'd18));
  assert property (data == shifter);

  // Startbit detection occurs only from idle on 1->0 transition history
  assert property (startbit |-> idle && (hhN[2:1] == 2'b10));

  // hh shift register tracks uart_rx
  assert property (1 |=> hh == {$past(hh[1:0]), $past(uart_rx)});

  // Bitcount next-state
  assert property (startbit |=> bitcount == 5'd0);
  assert property ((!idle && !valid && ser_clk) |=> bitcount == $past(bitcount) + 1);
  assert property ((valid && rd) |=> bitcount == 5'b11111);
  assert property (!startbit && !( (!idle && !valid && ser_clk) || (valid && rd) )
                   |=> bitcount == $past(bitcount));

  // Sample gating and shifter update
  assert property (sample |-> (bitcount > 5'd2) && bitcount[0] && !valid && ser_clk);
  assert property (sample |=> shifter == {$past(hh[1]), $past(shifter[7:1])});
  assert property (!sample |=> shifter == $past(shifter));

  // While valid and not read, data and bitcount hold
  assert property (valid && !rd |=> (data == $past(data) && bitcount == 5'd18));

  // RX coverage: detect start, reach valid, then read
  cover property (startbit ##[1:64] valid ##1 rd);
endmodule


// ---------------- buart (top wrapper) ----------------
bind buart buart_sva();
module buart_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetq);

  // Basic connectivity sanity (to submodules)
  assert property (busy == _tx.uart_busy);
  assert property (tx   == _tx.uart_tx);
  assert property (valid == _rx.valid);
  assert property (rx_data == _rx.data);

  // Top-level coverage: observe one TX and one RX transaction
  cover property (wr && !_tx.uart_busy ##1 ((_tx.sending && _tx.ser_clk)[*10]) ##1 !_tx.sending);
  cover property (_rx.startbit ##[1:64] _rx.valid ##1 rd);
endmodule
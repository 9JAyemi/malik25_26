// SVA for UART_Tx
// Bind into DUT to observe internal signals
module UART_Tx_sva #(parameter int CLK_DIV = 1)
(
  input  logic                  CLK,
  input  logic                  RST,
  input  logic                  WR,
  input  logic [7:0]            D,
  input  logic                  TX,
  input  logic                  TXE,
  input  logic                  CLK_B,
  input  logic                  prev_CLK_B,
  input  logic [$clog2(CLK_DIV)-1:0] baud_counter,
  input  logic [9:0]            send_reg,
  input  logic [3:0]            counter
);

  default clocking cb @(posedge CLK); endclocking

  // Basic signal consistency
  assert property (TX == send_reg[0]);

  // Reset behavior (next-cycle after RST high)
  assert property (RST |-> ##1 (send_reg == 10'h3FF && counter == 4'd0 && TXE == 1'b1));

  // prev_CLK_B tracks prior CLK_B
  assert property (disable iff (RST) prev_CLK_B == $past(CLK_B));

  // Baud divider in-range and behavior
  assert property (baud_counter < CLK_DIV);
  assert property (disable iff (RST)
                   (baud_counter == (CLK_DIV-1)) |-> ##1 (baud_counter == '0 && CLK_B != $past(CLK_B)));
  assert property (disable iff (RST)
                   (baud_counter != (CLK_DIV-1)) |-> ##1 (baud_counter == $past(baud_counter)+1 && CLK_B == $past(CLK_B)));
  assert property (disable iff (RST)
                   (CLK_B != $past(CLK_B)) |-> $past(baud_counter == (CLK_DIV-1)));

  // Write acceptance
  assert property (disable iff (RST)
                   (WR && TXE) |-> ##1 (send_reg[9:2] == D && send_reg[1] == 1'b0 && send_reg[0] == 1'b1
                                         && counter == 4'd10 && TXE == 1'b0));

  // Shift on baud rising edge (unless a write is accepted that cycle)
  sequence b_rise; (CLK_B && !prev_CLK_B); endsequence

  // Shift register update
  assert property (disable iff (RST)
                   (b_rise && !(WR && TXE)) |-> ##1 (send_reg == {1'b1, $past(send_reg[9:1])}));

  // Counter/TXE updates while shifting
  assert property (disable iff (RST)
                   (b_rise && !(WR && TXE) && (counter > 0)) |-> ##1 (counter == $past(counter)-1 && TXE == $past(TXE)));
  assert property (disable iff (RST)
                   (b_rise && !(WR && TXE) && (counter == 0)) |-> ##1 (counter == 0 && TXE == 1'b1));

  // TXE must be low while there are bits remaining
  assert property (disable iff (RST) (counter > 0) |-> (TXE == 1'b0));

  // TXE may rise only on a baud rising edge after counter reached 0
  assert property (disable iff (RST)
                   $rose(TXE) |-> ($past(b_rise) && $past(counter == 0)));

  // Optional: idle shifting when TXE=1 (keeps sending 1's), counter stays 0
  assert property (disable iff (RST)
                   (b_rise && TXE && !WR) |-> ##1 (send_reg == {1'b1, $past(send_reg[9:1])} && counter == 0 && TXE == 1));

  // Coverage

  // One complete transaction eventually completes (TXE returns high)
  cover property (disable iff (RST) (WR && TXE) ##[1:(2*CLK_DIV*20)] $rose(TXE));

  // Corner: write coincident with baud rising edge
  cover property (disable iff (RST) (WR && TXE && b_rise));

  // Baud counter rollover
  cover property (disable iff (RST) (baud_counter == (CLK_DIV-1)) ##1 (baud_counter == '0));

endmodule

// Bind into DUT; expose internal signals to SVA
bind UART_Tx UART_Tx_sva #(.CLK_DIV(CLOCK/(BAUD_RATE*2))) u_uart_tx_sva (
  .CLK(CLK),
  .RST(RST),
  .WR(WR),
  .D(D),
  .TX(TX),
  .TXE(TXE),
  .CLK_B(CLK_B),
  .prev_CLK_B(prev_CLK_B),
  .baud_counter(baud_counter),
  .send_reg(send_reg),
  .counter(counter)
);
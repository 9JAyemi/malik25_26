// SVA for RS232TX and RS232Baud. Bind these to the DUTs.

module RS232TX_sva (
  input logic        clk,
  input logic        Tx_start,
  input logic [23:0] dbuffer,
  input logic        Tx,
  input logic        Tx_busy,
  input logic        bittick,
  input logic [7:0]  Tx_data,
  input logic [3:0]  Tx_state,
  input logic [7:0]  Tx_shift
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (!$isunknown({Tx,Tx_busy,Tx_state,Tx_shift,bittick}));

  // Busy/ready relationship
  assert property (Tx_busy == (Tx_state != 4'h0));

  // State holding rules
  assert property (Tx_state==4'h0 && !Tx_start |=> Tx_state==4'h0);
  assert property ((Tx_state!=4'h0 && !bittick) |=> $stable(Tx_state));

  // Start: capture byte, enter start state, drive start bit low
  assert property (Tx_state==4'h0 && Tx_start
                   |=> Tx_state==4'h4 && Tx_busy && Tx_shift==$past(Tx_data) && Tx==1'b0);

  // Start bit stays low while in 0x4
  assert property (Tx_state==4'h4 |-> Tx==1'b0);

  // Idle/stop levels high
  assert property ((Tx_state<4 && Tx_state!=4'h4) |-> Tx==1'b1);

  // Shifter behavior in data states on bittick
  assert property ((Tx_state[3] && bittick)
                   |=> Tx_shift == {1'b0, $past(Tx_shift[7:1])});

  // Data-state transitions and bit output (LSB-first)
  assert property (((Tx_state inside {4'h8,4'h9,4'hA,4'hB,4'hC,4'hD,4'hE}) && bittick)
                   |=> (Tx_state == $past(Tx_state)+1 && Tx == $past(Tx_shift[1])));

  // Last data bit -> stop1
  assert property ((Tx_state==4'hF && bittick)
                   |=> (Tx_state==4'h2 && Tx==1'b1));

  // Stop1 -> Stop2
  assert property ((Tx_state==4'h2 && bittick)
                   |=> (Tx_state==4'h3 && Tx==1'b1));

  // Stop2 -> Idle; busy clears
  assert property ((Tx_state==4'h3 && bittick)
                   |=> (Tx_state==4'h0 && Tx==1'b1 && !Tx_busy));

  // Default recovery from illegal state on tick
  assert property ((!(Tx_state inside {4'h0,4'h2,4'h3,4'h4,4'h8,4'h9,4'hA,4'hB,4'hC,4'hD,4'hE,4'hF}) && bittick)
                   |=> Tx_state==4'h0);

  // Coverage: full 1-start + 8-data + 2-stop + idle handoff
  cover property (
    Tx_state==4'h0 && Tx_start ##1 Tx_state==4'h4
    ##[1:$] (bittick ##1 Tx_state==4'h8)
    ##[1:$] (bittick ##1 Tx_state==4'h9)
    ##[1:$] (bittick ##1 Tx_state==4'hA)
    ##[1:$] (bittick ##1 Tx_state==4'hB)
    ##[1:$] (bittick ##1 Tx_state==4'hC)
    ##[1:$] (bittick ##1 Tx_state==4'hD)
    ##[1:$] (bittick ##1 Tx_state==4'hE)
    ##[1:$] (bittick ##1 Tx_state==4'hF)
    ##[1:$] (bittick ##1 Tx_state==4'h2)
    ##[1:$] (bittick ##1 Tx_state==4'h3)
    ##[1:$] (bittick ##1 (Tx_state==4'h0 && !Tx_busy))
  );

  // Coverage: exercise both LSBs at start; and Tx_start during busy
  cover property (Tx_state==4'h0 && Tx_start && Tx_data[0]==1'b0);
  cover property (Tx_state==4'h0 && Tx_start && Tx_data[0]==1'b1);
  cover property (Tx_busy && Tx_start);
endmodule

bind RS232TX RS232TX_sva i_RS232TX_sva (
  .clk(clk),
  .Tx_start(Tx_start),
  .dbuffer(dbuffer),
  .Tx(Tx),
  .Tx_busy(Tx_busy),
  .bittick(bittick),
  .Tx_data(Tx_data),
  .Tx_state(Tx_state),
  .Tx_shift(Tx_shift)
);

module RS232Baud_sva (
  input logic clk,
  input logic enable,
  input logic tick
);
  default clocking cb @(posedge clk); endclocking

  // When disabled, tick must be stable
  assert property (!enable |=> $stable(tick));

  // Coverage: tick changes while enabled
  cover property (enable ##[1:$] $changed(tick));
endmodule

bind RS232Baud RS232Baud_sva i_RS232Baud_sva (
  .clk(clk),
  .enable(enable),
  .tick(tick)
);
// SVA for uart_tx_8n1
module uart_tx_8n1_sva (
    input  logic        clk,
    input  logic [7:0]  txbyte,
    input  logic        senddata,
    input  logic        txdone,
    input  logic        tx,
    input  logic [3:0]  state,
    input  logic [7:0]  data,
    input  logic        startbit,
    input  logic [2:0]  bitcount
);
  default clocking cb @(posedge clk); endclocking

  // txdone mapping and DONE stickiness
  assert property (txdone == (state == 3'b100));
  assert property ($past(state==3'b100) |-> (state==3'b100 && txdone && tx==1'b1));

  // Outputs by state
  assert property (state==3'b000 |-> tx==1'b1);
  assert property (state==3'b001 |-> tx==1'b0);
  assert property (state==3'b011 |-> tx==1'b1);
  assert property (state==3'b100 |-> tx==1'b1);

  // Idle hold when not sending
  assert property ($past(state==3'b000) && !$past(senddata) |-> state==3'b000);

  // Handshake capture and next-state
  assert property (state==3'b000 && senddata |=> state==3'b001
                                          && data == $past(txbyte)
                                          && bitcount == 3'b000
                                          && startbit == 1'b0);

  // Start -> Data and startbit rise afterwards
  assert property ($past(state==3'b001) |-> state==3'b010 && startbit==1'b1);

  // Data-path correctness
  assert property (state==3'b010 |-> tx == $past(data[0]));
  assert property ($past(state==3'b010) |-> data == {$past(data[6:0]),1'b0});
  assert property ($past(state==3'b010) |-> bitcount == $past(bitcount)+1);

  // Data exit condition and stay-when-not-last
  assert property ($past(state==3'b010) && $past(bitcount)==3'b111 |-> state==3'b011);
  assert property ($past(state==3'b010) && $past(bitcount)!=3'b111 |-> state==3'b010);

  // Stop -> Done
  assert property ($past(state==3'b011) |-> state==3'b100);

  // End-to-end 8N1 frame and bitstream check
  property p_tx_8n1_frame;
    bit [7:0] b;
    (state==3'b000 && senddata, b = txbyte) |=> // n+1
    state==3'b001 ##1
    (state==3'b010 && tx==b[0]) ##1
    (state==3'b010 && tx==b[1]) ##1
    (state==3'b010 && tx==b[2]) ##1
    (state==3'b010 && tx==b[3]) ##1
    (state==3'b010 && tx==b[4]) ##1
    (state==3'b010 && tx==b[5]) ##1
    (state==3'b010 && tx==b[6]) ##1
    (state==3'b010 && tx==b[7]) ##1
    (state==3'b011 && tx==1'b1) ##1
    (state==3'b100 && txdone && tx==1'b1);
  endproperty
  assert property (p_tx_8n1_frame);

  // Coverage
  cover property (p_tx_8n1_frame);
  cover property (state==3'b000 && senddata && txbyte[0]==1'b0);
  cover property (state==3'b000 && senddata && txbyte[0]==1'b1);
endmodule

// Bind into DUT
bind uart_tx_8n1 uart_tx_8n1_sva u_uart_tx_8n1_sva (
  .clk(clk),
  .txbyte(txbyte),
  .senddata(senddata),
  .txdone(txdone),
  .tx(tx),
  .state(state),
  .data(data),
  .startbit(startbit),
  .bitcount(bitcount)
);
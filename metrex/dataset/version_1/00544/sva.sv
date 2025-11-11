// SVA for fsm2: concise, high-quality checks and coverage
// Bind into DUT to access internals
module fsm2_sva
(
  input  logic        clk,
  input  logic        rst,
  input  logic        rxd,
  input  logic [7:0]  data,
  input  logic        received,

  // internal regs
  input  logic [1:0]  state,
  input  logic [7:0]  tmp_data,
  input  logic        tmp_received,
  input  logic [2:0]  index,
  input  logic [1:0]  rxd_hist
);
  localparam STATE1 = 2'b00;
  localparam STATE2 = 2'b01;
  localparam STATE3 = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Sanity/encoding
  assert property (state inside {STATE1,STATE2,STATE3});
  assert property (!$isunknown({state,received,data})); // outputs/state known
  assert property (data == tmp_data);
  assert property (received == tmp_received);

  // Start-of-frame detect causes transition and side effects
  assert property ( ($past(state)==STATE1 && $past(rxd_hist)==2'b00 && $past(rxd)==1)
                    |-> (state==STATE2 && rxd_hist==2'b11 && tmp_data==8'h00 && index==3'b000) );

  // No spurious STATE2 entry
  assert property ( (state==STATE2 && $past(state)==STATE1)
                    |-> ($past(rxd_hist)==2'b00 && $past(rxd)==1) );

  // rxd_hist shift while staying in STATE1
  assert property ( ($past(state)==STATE1 && state==STATE1)
                    |-> rxd_hist == {$past(rxd_hist[0]), $past(rxd)} );

  // Legal transitions only
  assert property ( $past(state)==STATE1 |-> state inside {STATE1,STATE2} );
  assert property ( $past(state)==STATE2 |-> state inside {STATE2,STATE3} );
  assert property ( $past(state)==STATE3 |-> state==STATE1 );

  // rxd_hist stable when coming from STATE2
  assert property ( $past(state)==STATE2 |-> rxd_hist == $past(rxd_hist) );

  // While in STATE2 (prev cycle), the written bit matches sampled rxd
  assert property ( $past(state)==STATE2 |-> tmp_data[$past(index)] == $past(rxd) );

  // Completion exactly after 8 bits
  assert property ( ($past(state)==STATE1 && $past(rxd_hist)==2'b00 && $past(rxd)==1)
                    |-> (state==STATE2)
                        ##1 (state==STATE2)[*6]
                        ##1 (state==STATE3 && received) );

  // Receive pulse properties
  assert property ( received |-> state==STATE3 );
  assert property ( received |=> !received );

  // Data contents on receive (LSB-first over 8 cycles)
  assert property ( received |-> ( data[0]==$past(rxd,8)
                                && data[1]==$past(rxd,7)
                                && data[2]==$past(rxd,6)
                                && data[3]==$past(rxd,5)
                                && data[4]==$past(rxd,4)
                                && data[5]==$past(rxd,3)
                                && data[6]==$past(rxd,2)
                                && data[7]==$past(rxd,1) ) );

  // After STATE3, clear and return to IDLE
  assert property ( $past(state)==STATE3 |-> (state==STATE1 && tmp_data==8'h00 && !received) );

  // Coverage: observe a full good transaction
  cover property ( ($past(state)==STATE1 && $past(rxd_hist)==2'b00 && $past(rxd)==1)
                   |-> (state==STATE2)
                       ##1 (state==STATE2)[*6]
                       ##1 (state==STATE3 && received)
                       ##1 (state==STATE1) );
endmodule

// Bind into all fsm2 instances (tool must allow binding to internals)
bind fsm2 fsm2_sva sva_i
(
  .clk(clk),
  .rst(rst),
  .rxd(rxd),
  .data(data),
  .received(received),
  .state(state),
  .tmp_data(tmp_data),
  .tmp_received(tmp_received),
  .index(index),
  .rxd_hist(rxd_hist)
);
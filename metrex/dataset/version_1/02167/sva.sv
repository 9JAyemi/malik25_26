// SVA for rgbmatrix
// Bind into DUT: bind rgbmatrix rgbmatrix_sva sva (.*);

module rgbmatrix_sva (
  input logic clk, rst,
  input logic R0,G0,B0,R1,G1,B1,
  input logic A,B,C,D,
  input logic MATCLK,MATLAT,MATOE,
  input logic [2:0] state,
  input logic [10:0] timer,
  input logic [3:0] delay,
  input logic [3:0] rd_row,
  input logic [1:0] rd_bit,
  input logic [4:0] rd_col
);

  // mirror DUT encodings
  localparam int WAIT=0, BLANK=1, LATCH=2, UNBLANK=3, READ=4, SHIFT1=5, SHIFT2=6;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // reset checks (active during reset)
  assert property (@(posedge clk) rst |-> R0==0 && G0==0 && B0==0 &&
                                    R1==0 && G1==0 && B1==0 &&
                                    A==0 && B==0 && C==0 && D==0 &&
                                    MATCLK==0 && MATLAT==0 && MATOE==1 &&
                                    state==READ &&
                                    timer==0 && delay==0 &&
                                    rd_row==0 && rd_bit==0 && rd_col==0);

  // state encoding
  assert property (state inside {WAIT,BLANK,LATCH,UNBLANK,READ,SHIFT1,SHIFT2});

  // timer behavior
  assert property (timer>0 |=> timer == $past(timer)-11'd1);
  assert property (timer==0 && rd_bit==2'd0 |=> timer==11'd191);
  assert property (timer==0 && rd_bit==2'd1 |=> timer==11'd383);
  assert property (timer==0 && rd_bit==2'd2 |=> timer==11'd767);
  assert property (timer==0 && rd_bit==2'd3 |=> timer==11'd1535);

  // WAIT
  assert property (state==WAIT && timer>0 |=> state==WAIT);
  assert property (state==WAIT && timer==0 |=> state==BLANK && MATOE==1 && delay==4'd8);
  assert property (state==WAIT |=> MATCLK==0);

  // BLANK
  assert property (state==BLANK && delay>0 |=> state==BLANK && delay==$past(delay)-1);
  assert property (state==BLANK && delay==0 |=> state==LATCH && delay==4'd8 && MATLAT==1);
  assert property (state==BLANK && delay==0 |=> {A,B,C,D} == $past({rd_row[0],rd_row[1],rd_row[2],rd_row[3]}));

  // LATCH
  assert property (state==LATCH && delay>0 |=> state==LATCH && delay==$past(delay)-1 && MATLAT==1);
  assert property (state==LATCH && delay==0 |=> state==UNBLANK && MATOE==0 && MATLAT==0);

  // UNBLANK: counters advance, col reset
  assert property (state==UNBLANK && rd_bit!=2'd3 |=> state==READ && rd_bit==$past(rd_bit)+1 && rd_col==0);
  assert property (state==UNBLANK && rd_bit==2'd3 && rd_row!=4'd15 |=> state==READ && rd_bit==0 && rd_row==$past(rd_row)+1 && rd_col==0);
  assert property (state==UNBLANK && rd_bit==2'd3 && rd_row==4'd15 |=> state==READ && rd_bit==0 && rd_row==0 && rd_col==0);

  // READ
  assert property (state==READ |=> state==SHIFT1 && MATCLK==0);

  // SHIFT1: data drive
  assert property (state==SHIFT1 |=> state==SHIFT2 &&
                   R0==$past(rd_row[0]) && G0==$past(rd_row[1]) && B0==0 &&
                   R1==0 && G1==$past(rd_row[1]) && B1==0);

  // SHIFT2: clock pulse and column count
  assert property (state==SHIFT2 && rd_col!=5'd31 |=> state==READ && rd_col==$past(rd_col)+1 && MATCLK==1);
  assert property (state==SHIFT2 && rd_col==5'd31 |=> state==WAIT && rd_col==0 && MATCLK==1);

  // stability where not written
  assert property (!(state inside {SHIFT2,UNBLANK}) |=> rd_col==$past(rd_col));
  assert property (state!=UNBLANK |=> rd_bit==$past(rd_bit) && rd_row==$past(rd_row));

  // signal domain constraints
  assert property (rd_row <= 4'd15 && rd_bit <= 2'd3 && rd_col <= 5'd31);
  assert property (MATLAT |-> state==LATCH);
  assert property (state inside {UNBLANK,READ,SHIFT1,SHIFT2} |-> MATOE==0);

  // coverage
  cover property (state==WAIT && timer==0 ##1 state==BLANK ##1 state==LATCH ##1 state==UNBLANK ##1 state==READ ##1 state==SHIFT1 ##1 state==SHIFT2);
  cover property (state==SHIFT2 && rd_col==5'd31 ##1 state==WAIT);
  cover property (state==UNBLANK && rd_bit==2'd3 && rd_row==4'd15 ##1 state==READ && rd_bit==0 && rd_row==0);
endmodule

// Bind this checker to the DUT
bind rgbmatrix rgbmatrix_sva sva (.*);
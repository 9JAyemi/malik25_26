// SVA for module Keyboard
// Bind this file to the DUT: bind Keyboard Keyboard_sva i_keyboard_sva(.*);

module Keyboard_sva(
  input  logic        Clock,
  input  logic [3:0]  C,
  input  logic        press,
  input  logic [3:0]  CodeOut,
  input  logic [3:0]  R,
  input  logic [2:0]  state,
  input  logic [2:0]  flag
);

  localparam logic [2:0] KeyNo  = 3'b000,
                         State1 = 3'b001,
                         State2 = 3'b010,
                         State3 = 3'b011,
                         State4 = 3'b100,
                         KeyYes = 3'b101;

  default clocking cb @(posedge Clock); endclocking
  default disable iff ($isunknown({state,C,R,flag,press,CodeOut}));

  // Encoding/legal-value checks
  assert property (state inside {KeyNo,State1,State2,State3,State4,KeyYes});
  assert property (R inside {4'b0000,4'b0111,4'b1011,4'b1101,4'b1110});
  assert property (flag <= 3'd7);
  assert property (state==KeyNo |-> R==4'b0000);
  assert property (press |-> state==KeyYes);

  // State transitions and R updates when scanning (C==1111)
  assert property (state==KeyNo  && C==4'b1111 |=> state==KeyNo  && R==4'b0000);
  assert property (state==KeyNo  && C!=4'b1111 |=> state==State1 && R==4'b0111);
  assert property (state==State1 && C==4'b1111 |=> state==State2 && R==4'b1011);
  assert property (state==State2 && C==4'b1111 |=> state==State3 && R==4'b1101);
  assert property (state==State3 && C==4'b1111 |=> state==State4 && R==4'b1110);
  assert property (state==State4 && C==4'b1111 |=> state==KeyNo  && R==4'b0000);

  // On detection (C!=1111) during scan, must enter KeyYes next
  assert property ((state inside {State1,State2,State3,State4}) && C!=4'b1111 |=> state==KeyYes);

  // KeyYes behavior: release/reset on C==1111, debounce and press on hold
  assert property (state==KeyYes && C==4'b1111 |=> state==KeyNo && R==4'b0000 && press==0 && flag==0);
  assert property (state==KeyYes && C!=4'b1111 |=> state==KeyYes && $stable(R));
  assert property (state==KeyYes && C!=4'b1111 && $past(state==KeyYes && C!=4'b1111) && $past(flag)<7
                   |-> flag==$past(flag)+1 && press==0);
  assert property (state==KeyYes && C!=4'b1111 && flag>=7 |=> press==1 && state==KeyYes && flag>=7);

  // Combinational decoder correctness (both directions)
  assert property (({C,R}==8'b0111_0111) |-> CodeOut==4'h1);
  assert property (({C,R}==8'b0111_1011) |-> CodeOut==4'h4);
  assert property (({C,R}==8'b0111_1101) |-> CodeOut==4'h7);
  assert property (({C,R}==8'b0111_1110) |-> CodeOut==4'hA);

  assert property (({C,R}==8'b1011_0111) |-> CodeOut==4'h2);
  assert property (({C,R}==8'b1011_1011) |-> CodeOut==4'h5);
  assert property (({C,R}==8'b1011_1101) |-> CodeOut==4'h8);
  assert property (({C,R}==8'b1011_1110) |-> CodeOut==4'h0);

  assert property (({C,R}==8'b1101_0111) |-> CodeOut==4'h3);
  assert property (({C,R}==8'b1101_1011) |-> CodeOut==4'h6);
  assert property (({C,R}==8'b1101_1101) |-> CodeOut==4'h9);
  assert property (({C,R}==8'b1101_1110) |-> CodeOut==4'hB);

  assert property (({C,R}==8'b1110_0111) |-> CodeOut==4'hC);
  assert property (({C,R}==8'b1110_1011) |-> CodeOut==4'hD);
  assert property (({C,R}==8'b1110_1101) |-> CodeOut==4'hE);

  assert property ((CodeOut!=4'hF) |-> ({C,R} inside {
    8'b0111_0111,8'b0111_1011,8'b0111_1101,8'b0111_1110,
    8'b1011_0111,8'b1011_1011,8'b1011_1101,8'b1011_1110,
    8'b1101_0111,8'b1101_1011,8'b1101_1101,8'b1101_1110,
    8'b1110_0111,8'b1110_1011,8'b1110_1101
  }));

  // Coverage
  sequence full_scan;
    state==KeyNo  && C==4'b1111 ##1
    state==State1 && C==4'b1111 ##1
    state==State2 && C==4'b1111 ##1
    state==State3 && C==4'b1111 ##1
    state==State4 && C==4'b1111 ##1
    state==KeyNo;
  endsequence
  cover property (full_scan);

  cover property (state==KeyYes && C!=4'b1111 && flag==0 ##7 (press && flag>=7));

  // Cover each key decode occurrence
  cover property ({C,R}==8'b0111_0111 && CodeOut==4'h1);
  cover property ({C,R}==8'b0111_1011 && CodeOut==4'h4);
  cover property ({C,R}==8'b0111_1101 && CodeOut==4'h7);
  cover property ({C,R}==8'b0111_1110 && CodeOut==4'hA);
  cover property ({C,R}==8'b1011_0111 && CodeOut==4'h2);
  cover property ({C,R}==8'b1011_1011 && CodeOut==4'h5);
  cover property ({C,R}==8'b1011_1101 && CodeOut==4'h8);
  cover property ({C,R}==8'b1011_1110 && CodeOut==4'h0);
  cover property ({C,R}==8'b1101_0111 && CodeOut==4'h3);
  cover property ({C,R}==8'b1101_1011 && CodeOut==4'h6);
  cover property ({C,R}==8'b1101_1101 && CodeOut==4'h9);
  cover property ({C,R}==8'b1101_1110 && CodeOut==4'hB);
  cover property ({C,R}==8'b1110_0111 && CodeOut==4'hC);
  cover property ({C,R}==8'b1110_1011 && CodeOut==4'hD);
  cover property ({C,R}==8'b1110_1101 && CodeOut==4'hE);
  cover property (CodeOut==4'hF);

endmodule

// Bind into the DUT
bind Keyboard Keyboard_sva i_keyboard_sva(.*);
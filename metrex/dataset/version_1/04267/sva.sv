// Bind these SVA to the DUT
bind FSM FSM_SVA fsm_sva_i (
  .clk(clk),
  .reset(reset),
  .state(state),
  .rom_addr(rom_addr),
  .rom_q(rom_q),
  .ram_a_addr(ram_a_addr),
  .ram_b_addr(ram_b_addr),
  .ram_b_w(ram_b_w),
  .pe(pe),
  .done(done),
  .loop1(loop1),
  .loop2(loop2),
  .count(count),
  .op(op),
  .times(times),
  .src1(src1),
  .src2(src2),
  .dest(dest)
);

module FSM_SVA(
  input logic              clk,
  input logic              reset,
  input logic [5:0]        state,
  input logic [8:0]        rom_addr,
  input logic [28:0]       rom_q,
  input logic [5:0]        ram_a_addr,
  input logic [5:0]        ram_b_addr,
  input logic              ram_b_w,
  input logic [10:0]       pe,
  input logic              done,
  input logic [294:0]      loop1,
  input logic [294:0]      loop2,
  input logic [8:0]        count,
  input logic [1:0]        op,
  input logic [8:0]        times,
  input logic [5:0]        src1,
  input logic [5:0]        src2,
  input logic [5:0]        dest
);

  default clocking cb @(posedge clk); endclocking

  // Local mirror of DUT params/constants
  localparam logic [5:0] START=6'd0, READ_SRC1=6'd1, READ_SRC2=6'd2, CALC=6'd4, WAIT=6'd8, WRITE=6'd16, DON=6'd32;
  localparam logic [5:0] CMD_ADD=6'd4, CMD_SUB=6'd8, CMD_CUBIC=6'd16;
  localparam logic [1:0] ADD=2'd0, SUB=2'd1, CUBIC=2'd2, MULT=2'd3;
  localparam logic [8:0] LOOP1_START=9'd21, LOOP1_END=9'd116, LOOP2_START=9'd288, LOOP2_END=9'd301;

  // Reset effects
  assert property (reset |-> state==START && rom_addr==9'd0 && loop1=={295{1'b1}} && loop2=={295{1'b1}} && count==9'd0 && done==1'b0);

  // No X after reset deasserted
  assert property (disable iff (reset) !$isunknown({state,rom_addr,ram_a_addr,ram_b_addr,ram_b_w,pe,done,count,loop1[0],loop2[0]}));

  // State encoding and transitions
  assert property (disable iff (reset) state inside {START,READ_SRC1,READ_SRC2,CALC,WAIT,WRITE,DON});
  assert property (disable iff (reset) (state==START)    |-> state==READ_SRC1);
  assert property (disable iff (reset) (state==READ_SRC1)|-> state==READ_SRC2);
  assert property (disable iff (reset) (state==READ_SRC2 && times==0) |-> state==DON);
  assert property (disable iff (reset) (state==READ_SRC2 && times!=0) |-> state==CALC);
  assert property (disable iff (reset) (state==CALC && count==9'd1)   |-> state==WAIT);
  assert property (disable iff (reset) (state==CALC && count!=9'd1)   |-> state==CALC);
  assert property (disable iff (reset) (state==WAIT)   |-> state==WRITE);
  assert property (disable iff (reset) (state==WRITE)  |-> state==READ_SRC1);
  assert property (disable iff (reset) (state==DON)    |-> state==DON); // absorbing

  // Count behavior
  assert property (disable iff (reset) (state==READ_SRC1) |-> count==$past(times));
  assert property (disable iff (reset) (state==CALC)      |-> count==$past(count)-9'd1);
  assert property (disable iff (reset) !(state inside {READ_SRC1,CALC}) |-> count==$past(count));

  // Done behavior (registered)
  assert property (disable iff (reset) (state==DON) |-> done);
  assert property (disable iff (reset) done |-> $past(state)==DON);
  assert property (disable iff (reset) (state!=DON) |-> !done);

  // rom_addr update only in WAIT and with loop behavior
  assert property (disable iff (reset) (state!=WAIT) |-> rom_addr==$past(rom_addr));
  assert property (disable iff (reset) (state==WAIT && rom_addr==LOOP1_END && loop1[0]) |-> rom_addr==LOOP1_START);
  assert property (disable iff (reset) (state==WAIT && rom_addr==LOOP2_END && loop2[0]) |-> rom_addr==LOOP2_START);
  assert property (disable iff (reset)
                   (state==WAIT && !((rom_addr==LOOP1_END && loop1[0]) || (rom_addr==LOOP2_END && loop2[0])))
                   |-> rom_addr==$past(rom_addr)+9'd1);

  // loop shift registers
  assert property (disable iff (reset) (state==WAIT && rom_addr==LOOP1_END) |-> loop1==($past(loop1)>>1));
  assert property (disable iff (reset) !(state==WAIT && rom_addr==LOOP1_END) |-> loop1==$past(loop1));
  assert property (disable iff (reset) (state==WAIT && rom_addr==LOOP2_END) |-> loop2==($past(loop2)>>1));
  assert property (disable iff (reset) !(state==WAIT && rom_addr==LOOP2_END) |-> loop2==$past(loop2));

  // Combinational address controls
  assert property (disable iff (reset) (state==READ_SRC1) |=> ram_a_addr==src1);
  assert property (disable iff (reset) (state==READ_SRC2) |=> ram_a_addr==src2);
  assert property (disable iff (reset) !(state inside {READ_SRC1,READ_SRC2}) |=> ram_a_addr==6'd0);

  assert property (disable iff (reset) (state==READ_SRC1 && op==ADD)   |=> ram_b_addr==CMD_ADD);
  assert property (disable iff (reset) (state==READ_SRC1 && op==SUB)   |=> ram_b_addr==CMD_SUB);
  assert property (disable iff (reset) (state==READ_SRC1 && op==CUBIC) |=> ram_b_addr==CMD_CUBIC);
  assert property (disable iff (reset) (state==READ_SRC1 && op==MULT)  |=> ram_b_addr==6'd0);
  assert property (disable iff (reset) (state==READ_SRC2)              |=> ram_b_addr==src2);
  assert property (disable iff (reset) (state==WRITE)                  |=> ram_b_addr==dest);
  assert property (disable iff (reset) !(state inside {READ_SRC1,READ_SRC2,WRITE}) |=> ram_b_addr==6'd0);

  // Write enable mapping
  assert property (disable iff (reset) ram_b_w == (state==WRITE));

  // PE control (registered)
  assert property (disable iff (reset) (state==READ_SRC1 && (op==ADD || op==SUB)) |-> pe==11'b11001000000);
  assert property (disable iff (reset) (state==READ_SRC1 && op==CUBIC)            |-> pe==11'b11111000000);
  assert property (disable iff (reset) (state==READ_SRC1 && op==MULT)             |-> pe==11'b11110000000);

  assert property (disable iff (reset) (state==READ_SRC2 && (op==ADD || op==SUB)) |-> pe==11'b00110000000);
  assert property (disable iff (reset) (state==READ_SRC2 && op==CUBIC)            |-> pe==11'b00000000000);
  assert property (disable iff (reset) (state==READ_SRC2 && op==MULT)             |-> pe==11'b00001000000);

  assert property (disable iff (reset) (state==CALC && (op==ADD || op==SUB))      |-> pe==11'b00000010001);
  assert property (disable iff (reset) (state==CALC && op==CUBIC)                  |-> pe==11'b01010000001);
  assert property (disable iff (reset) (state==CALC && op==MULT)                   |-> pe==11'b00000111111);

  assert property (disable iff (reset) !(state inside {READ_SRC1,READ_SRC2,CALC})  |-> pe==11'b0);

  // Functional coverage
  cover property (disable iff (reset)
    (state==READ_SRC1 && times>0) ##1 (state==READ_SRC2 && times>0) ##1 (state==CALC)
      ##[1:$] (state==WAIT) ##1 (state==WRITE) ##1 (state==READ_SRC1));

  cover property (disable iff (reset) (state==READ_SRC2 && times==0) ##1 (state==DON) ##1 done);

  cover property (disable iff (reset) (state==WAIT && rom_addr==LOOP1_END && loop1[0]) ##1 (rom_addr==LOOP1_START));
  cover property (disable iff (reset) (state==WAIT && rom_addr==LOOP2_END && loop2[0]) ##1 (rom_addr==LOOP2_START));

  cover property (disable iff (reset) (state==READ_SRC1 && op==ADD   && times>0) ##1 (state==READ_SRC2)
                                     ##1 (state==CALC) ##[1:$] (state==WAIT) ##1 (state==WRITE));
  cover property (disable iff (reset) (state==READ_SRC1 && op==SUB   && times>0) ##1 (state==READ_SRC2)
                                     ##1 (state==CALC) ##[1:$] (state==WAIT) ##1 (state==WRITE));
  cover property (disable iff (reset) (state==READ_SRC1 && op==CUBIC && times>0) ##1 (state==READ_SRC2)
                                     ##1 (state==CALC) ##[1:$] (state==WAIT) ##1 (state==WRITE));
  cover property (disable iff (reset) (state==READ_SRC1 && op==MULT  && times>0) ##1 (state==READ_SRC2)
                                     ##1 (state==CALC) ##[1:$] (state==WAIT) ##1 (state==WRITE));

  cover property (disable iff (reset) (state==READ_SRC1 && times==9'd1) ##1 (state==READ_SRC2)
                                     ##1 (state==CALC && count==9'd1) ##1 (state==WAIT));

  cover property (disable iff (reset) (state==WRITE) && ram_b_w);

endmodule
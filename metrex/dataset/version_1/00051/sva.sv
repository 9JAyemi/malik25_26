// SVA for I2C_WRITE_WDATA
// Bind this module to the DUT: bind I2C_WRITE_WDATA I2C_WRITE_WDATA_sva sva(.RESET_N, .PT_CK, .GO, .REG_DATA, .SLAVE_ADDRESS, .SDAI, .SDAO, .SCLO, .END_OK, .ST, .CNT, .BYTE, .ACK_OK, .BYTE_NUM);

module I2C_WRITE_WDATA_sva (
  input         RESET_N,
  input         PT_CK,
  input         GO,
  input  [15:0] REG_DATA,
  input  [7:0]  SLAVE_ADDRESS,
  input         SDAI,
  input         SDAO,
  input         SCLO,
  input         END_OK,
  input  [7:0]  ST,
  input  [7:0]  CNT,
  input  [7:0]  BYTE,
  input         ACK_OK,
  input  [7:0]  BYTE_NUM
);

  // Internal A is not exposed; we can still assert behaviors that affect outputs and visible regs.
  // If A is made visible, uncomment and connect it, then enable the A-related assertions below.
  // input  [8:0]  A;

  default clocking cb @(posedge PT_CK); endclocking
  default disable iff (!RESET_N);

  // Legal state encoding
  assert property (ST inside {8'd0,8'd1,8'd2,8'd3,8'd4,8'd5,8'd6,8'd7,8'd8,8'd9,8'd30,8'd31});

  // Reset drives ST to 0 within one cycle
  assert property ($fell(RESET_N) |=> ST==8'd0);

  // State 0 (idle) outputs and transitions
  assert property ($past(ST)==8'd0 |-> SDAO==1'b1 && SCLO==1'b1 && ACK_OK==1'b0 && CNT==8'd0 && END_OK==1'b1 && BYTE==8'd0);
  assert property ($past(ST)==8'd0 && GO  |-> ST==8'd30);
  assert property ($past(ST)==8'd0 && !GO |-> ST==8'd0);

  // State 30: wait for GO deassert
  assert property ($past(ST)==8'd30 &&  GO |-> ST==8'd30);
  assert property ($past(ST)==8'd30 && !GO |-> ST==8'd31);

  // State 31: start sequence
  assert property ($past(ST)==8'd31 |-> ST==8'd1 && END_OK==1'b0 && ACK_OK==1'b0);

  // State 1: load address, SCL=1, SDA set for start bit stretching
  assert property ($past(ST)==8'd1 |-> ST==8'd2 && {SDAO,SCLO}==2'b01);
  // If A were visible: assert property ($past(ST)==8'd1 |-> A=={SLAVE_ADDRESS,1'b1});

  // State 2: drive both low
  assert property ($past(ST)==8'd2 |-> ST==8'd3 && {SDAO,SCLO}==2'b00);

  // State 3: shift out next bit on SDA (MSB-first), advance shift register
  // Outputs
  // If A were visible:
  //   assert property ($past(ST)==8'd3 |-> SDAO==$past(A[8]) && A=={$past(A[7:0]),1'b0});
  // Without A visibility, ensure SDAO is stable low/high only through states driving it:
  assert property ($past(ST)==8'd3 |-> ST==8'd4);

  // State 4: SCL high, increment bit count
  assert property ($past(ST)==8'd4 |-> ST==8'd5 && SCLO==1'b1 && CNT==$past(CNT)+8'd1);

  // State 5: SCL low, branch on bit count and byte progress
  assert property ($past(ST)==8'd5 |-> SCLO==1'b0);

  // If not yet 9 bits, loop back to state 2
  assert property ($past(ST)==8'd5 && $past(CNT)!=8'd9 |-> ST==8'd2);

  // At 9 bits and last byte done -> go to state 6 (stop sequence)
  assert property ($past(ST)==8'd5 && $past(CNT)==8'd9 && $past(BYTE)==$past(BYTE_NUM) |-> ST==8'd6);

  // At 9 bits and more bytes pending -> clear CNT and continue at state 2
  assert property ($past(ST)==8'd5 && $past(CNT)==8'd9 && $past(BYTE)!=$past(BYTE_NUM) |-> ST==8'd2 && CNT==8'd0);

  // Byte/data programming on rollover (if exactly BYTE==0 or 1)
  // If A were visible, enable these two for full datapath checking:
  // assert property ($past(ST)==8'd5 && $past(CNT)==8'd9 && $past(BYTE)==8'd0 && $past(BYTE_NUM)!=8'd0 |-> ST==8'd2 && CNT==8'd0 && BYTE==8'd1 && A=={REG_DATA[15:8],1'b1});
  // assert property ($past(ST)==8'd5 && $past(CNT)==8'd9 && $past(BYTE)==8'd1 && $past(BYTE_NUM)!=8'd1 |-> ST==8'd2 && CNT==8'd0 && BYTE==8'd2 && A=={REG_DATA[7:0],1'b1});

  // "ACK_OK" set when SDAI observed high at 9th bit sample
  assert property ($past(ST)==8'd5 && $past(CNT)==8'd9 && SDAI |-> ACK_OK==1'b1);

  // State 6/7/8: stop condition: 00 -> 01 -> 11
  assert property ($past(ST)==8'd6 |-> ST==8'd7 && {SDAO,SCLO}==2'b00);
  assert property ($past(ST)==8'd7 |-> ST==8'd8 && {SDAO,SCLO}==2'b01);
  assert property ($past(ST)==8'd8 |-> ST==8'd9 && {SDAO,SCLO}==2'b11);

  // State 9: return to idle-prep and then state 30
  assert property ($past(ST)==8'd9 |-> ST==8'd30 && SDAO==1'b1 && SCLO==1'b1 && CNT==8'd0 && END_OK==1'b1 && BYTE==8'd0);

  // Basic covers

  // Cover: handshake GO high->low to start a transaction
  cover property (ST==8'd0 && GO ##1 ST==8'd30 ##1 !GO ##1 ST==8'd31 ##1 ST==8'd1);

  // Cover: one full byte bit-cycle (2->3->4->5 loop through CNT!=9)
  cover property ($past(ST)==8'd2 ##1 ST==8'd3 ##1 ST==8'd4 ##1 ST==8'd5 && $past(CNT)!=8'd9 ##1 ST==8'd2);

  // Cover: rollover at 9th bit with more bytes pending (branch back to 2)
  cover property ($past(ST)==8'd5 && $past(CNT)==8'd9 && $past(BYTE)!=$past(BYTE_NUM) ##0 ST==8'd2);

  // Cover: final byte path to stop (5->6->7->8->9)
  cover property ($past(ST)==8'd5 && $past(CNT)==8'd9 && $past(BYTE)==$past(BYTE_NUM) ##0 ST==8'd6 ##1 ST==8'd7 ##1 ST==8'd8 ##1 ST==8'd9);

  // Cover: ACK_OK set on SDAI high at 9th bit
  cover property ($past(ST)==8'd5 && $past(CNT)==8'd9 && SDAI ##0 ACK_OK);

  // Cover: END_OK asserted at idle and after stop
  cover property ($past(ST)==8'd9 ##0 END_OK && ST==8'd30);
endmodule

// Example bind (uncomment in TB or a bind file):
// bind I2C_WRITE_WDATA I2C_WRITE_WDATA_sva sva (.*);
// SVA for SPIFSM. Bind into DUT to check/cover FSM behavior, timer, handshakes, and data path.

module SPIFSM_sva #(parameter SPPRWidth = 4,
                    parameter SPRWidth  = 4,
                    parameter DataWidth = 8)
(
  input  logic                  Reset_n_i,
  input  logic                  Clk_i,
  input  logic                  Start_i,
  input  logic                  SPI_Transmission_i,
  input  logic [DataWidth-1:0]  SPI_Data_i,
  input  logic                  SPI_FIFOFull_i,
  input  logic                  SPI_FIFOEmpty_i,
  input  logic [15:0]           ParamCounterPreset_i,

  input  logic                  Done_o,
  input  logic [DataWidth-1:0]  Byte0_o,
  input  logic [DataWidth-1:0]  Byte1_o,
  input  logic                  SPI_Write_o,
  input  logic                  SPI_ReadNext_o,
  input  logic [DataWidth-1:0]  SPI_Data_o,
  input  logic                  ADT7310CS_n_o,

  // internal DUT signals
  input  logic [3:0]            SPI_FSM_State,
  input  logic [15:0]           SPI_FSM_Timer,
  input  logic                  SPI_FSM_TimerPreset,
  input  logic                  SPI_FSM_TimerEnable,
  input  logic                  SPI_FSM_TimerOvfl,
  input  logic                  SPI_FSM_Wr1,
  input  logic                  SPI_FSM_Wr0
);

  // Mirror state encodings for readability
  localparam stIdle        = 4'b0000;
  localparam stWriteValue  = 4'b0001;
  localparam stWaitSent    = 4'b0010;
  localparam stConsume1    = 4'b0011;
  localparam stWait        = 4'b0100;
  localparam stWriteDummy1 = 4'b0101;
  localparam stWriteDummy2 = 4'b0110;
  localparam stRead1       = 4'b0111;
  localparam stRead2       = 4'b1000;
  localparam stRead3       = 4'b1001;
  localparam stPause       = 4'b1010;

  default clocking cb @(posedge Clk_i); endclocking
  default disable iff (!Reset_n_i)

  // Basic sanity / reset
  assert property (SPI_FSM_State inside {stIdle,stWriteValue,stWaitSent,stConsume1,stWait,stWriteDummy1,stWriteDummy2,stRead1,stRead2,stRead3,stPause});
  assert property (!Reset_n_i |-> (SPI_FSM_State==stIdle && Byte0_o=={DataWidth{1'b0}} && Byte1_o=={DataWidth{1'b0}} && SPI_FSM_Timer==16'd0));
  assert property (!$isunknown({ADT7310CS_n_o,SPI_Write_o,SPI_ReadNext_o,Done_o}));
  assert property (SPI_Write_o |-> !$isunknown(SPI_Data_o));
  assert property (!(SPI_Write_o && SPI_ReadNext_o));
  assert property (!(SPI_FSM_Wr0 && SPI_FSM_Wr1));

  // State/output semantics and transitions
  assert property ((SPI_FSM_State==stIdle && !Start_i) |-> (ADT7310CS_n_o && !SPI_Write_o && !SPI_ReadNext_o && Done_o));
  assert property ((SPI_FSM_State==stIdle &&  Start_i) |-> (ADT7310CS_n_o==1'b0 && SPI_Write_o && (SPI_Data_o==8'h08) && !Done_o) and ##1 (SPI_FSM_State==stWriteValue));

  assert property ((SPI_FSM_State==stWriteValue) |-> (ADT7310CS_n_o==1'b0 && SPI_Write_o && (SPI_Data_o==8'h20) && !Done_o) and ##1 (SPI_FSM_State==stWaitSent));

  assert property ((SPI_FSM_State==stWaitSent &&  SPI_Transmission_i)  |-> (ADT7310CS_n_o==1'b0 && !Done_o && !SPI_ReadNext_o && !SPI_FSM_TimerPreset) and ##1 (SPI_FSM_State==stWaitSent));
  assert property ((SPI_FSM_State==stWaitSent && !SPI_Transmission_i)  |-> (ADT7310CS_n_o==1'b0 && !Done_o &&  SPI_ReadNext_o &&  SPI_FSM_TimerPreset) and ##1 (SPI_FSM_State==stConsume1));

  assert property ((SPI_FSM_State==stConsume1) |-> (ADT7310CS_n_o==1'b0 && !Done_o && SPI_ReadNext_o && SPI_FSM_TimerEnable) and ##1 (SPI_FSM_State==stWait));

  assert property ((SPI_FSM_State==stWait && !SPI_FSM_TimerOvfl) |-> (ADT7310CS_n_o==1'b1 && !Done_o && SPI_FSM_TimerEnable && !SPI_Write_o) and ##1 (SPI_FSM_State==stWait));
  assert property ((SPI_FSM_State==stWait &&  SPI_FSM_TimerOvfl) |-> (ADT7310CS_n_o==1'b0 && !Done_o && SPI_Write_o && (SPI_Data_o==8'h50)) and ##1 (SPI_FSM_State==stWriteDummy1));

  assert property ((SPI_FSM_State==stWriteDummy1) |-> (ADT7310CS_n_o==1'b0 && !Done_o && SPI_Write_o && (SPI_Data_o==8'hFF)) and ##1 (SPI_FSM_State==stWriteDummy2));
  assert property ((SPI_FSM_State==stWriteDummy2) |-> (ADT7310CS_n_o==1'b0 && !Done_o && SPI_Write_o && (SPI_Data_o==8'hFF)) and ##1 (SPI_FSM_State==stRead1));

  assert property ((SPI_FSM_State==stRead1 &&  SPI_Transmission_i) |-> (ADT7310CS_n_o==1'b0 && !Done_o && !SPI_ReadNext_o) and ##1 (SPI_FSM_State==stRead1));
  assert property ((SPI_FSM_State==stRead1 && !SPI_Transmission_i) |-> (ADT7310CS_n_o==1'b0 && !Done_o &&  SPI_ReadNext_o) and ##1 (SPI_FSM_State==stRead2));

  assert property ((SPI_FSM_State==stRead2) |-> (!Done_o &&  SPI_ReadNext_o &&  SPI_FSM_Wr1 && !SPI_FSM_Wr0) and ##1 (SPI_FSM_State==stRead3));
  assert property ((SPI_FSM_State==stRead3) |-> (!Done_o &&  SPI_ReadNext_o &&  SPI_FSM_Wr0 && !SPI_FSM_Wr1) and ##1 (SPI_FSM_State==stPause));

  assert property ((SPI_FSM_State==stPause) |-> (ADT7310CS_n_o==1'b1 && Done_o && !SPI_Write_o && !SPI_ReadNext_o) and ##1 (SPI_FSM_State==stIdle));

  // Write strobes only in intended states
  assert property (SPI_FSM_Wr1 |-> (SPI_FSM_State==stRead2));
  assert property (SPI_FSM_Wr0 |-> (SPI_FSM_State==stRead3));

  // Byte capture correctness
  assert property (SPI_FSM_Wr1 |-> ##0 (Byte1_o == $past(SPI_Data_i)));
  assert property (SPI_FSM_Wr0 |-> ##0 (Byte0_o == $past(SPI_Data_i)));

  // Timer correctness
  assert property (SPI_FSM_TimerOvfl == (SPI_FSM_Timer==16'd0));
  assert property (SPI_FSM_TimerPreset |=> (SPI_FSM_Timer == ParamCounterPreset_i));
  assert property (!SPI_FSM_TimerPreset &&  SPI_FSM_TimerEnable |=> (SPI_FSM_Timer == $past(SPI_FSM_Timer) - 16'd1));
  assert property (!SPI_FSM_TimerPreset && !SPI_FSM_TimerEnable |=> (SPI_FSM_Timer == $past(SPI_FSM_Timer)));

  // Coverage: full transaction and key datapath values
  cover property ((SPI_FSM_State==stIdle && Start_i) ##1
                  (SPI_FSM_State==stWriteValue) ##1
                  (SPI_FSM_State==stWaitSent) ##[1:$]
                  (SPI_FSM_State==stConsume1) ##1
                  (SPI_FSM_State==stWait)     ##[1:$]
                  (SPI_FSM_State==stWriteDummy1) ##1
                  (SPI_FSM_State==stWriteDummy2) ##1
                  (SPI_FSM_State==stRead1)    ##[1:$]
                  (SPI_FSM_State==stRead2)    ##1
                  (SPI_FSM_State==stRead3)    ##1
                  (SPI_FSM_State==stPause)    ##1
                  (SPI_FSM_State==stIdle));

  cover property ((SPI_Write_o && (SPI_Data_o==8'h08)) ##1
                  (SPI_Write_o && (SPI_Data_o==8'h20)) ##[1:$]
                  (SPI_Write_o && (SPI_Data_o==8'h50)) ##1
                  (SPI_Write_o && (SPI_Data_o==8'hFF)) ##1
                  (SPI_Write_o && (SPI_Data_o==8'hFF)));

  cover property (SPI_FSM_Wr1 ##[1:8] SPI_FSM_Wr0);
  cover property ((SPI_FSM_State==stWait && !SPI_FSM_TimerOvfl && ADT7310CS_n_o) ##[1:$]
                  (SPI_FSM_State==stWait &&  SPI_FSM_TimerOvfl && !ADT7310CS_n_o));
endmodule

// Bind into DUT
bind SPIFSM SPIFSM_sva #(.SPPRWidth(SPPRWidth), .SPRWidth(SPRWidth), .DataWidth(DataWidth)) u_SPIFSM_sva (.*);
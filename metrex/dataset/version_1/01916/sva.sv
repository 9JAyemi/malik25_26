// SVA checker for DebugIR
// Bind this file to the DUT: bind DebugIR DebugIR_sva dbgir_sva(.*);

module DebugIR_sva (
    input  logic        clk,
    input  logic        rst,
    input  logic        ir,
    input  logic        ir0, ir1, ir2,
    input  logic        irPosEdge, irNegEdge, irChange,
    input  logic [10:0] counter1,
    input  logic [8:0]  counter2,
    input  logic        check9ms, check4ms, high, low,
    input  logic [2:0]  state,
    input  logic [2:0]  nextState,
    input  logic [5:0]  irDataPos,
    input  logic [31:0] irRead,
    input  logic        err,
    input  logic        stateOut,
    input  logic [3:0]  mode,
    input  logic        showName,
    input  logic [1:0]  cpuClkMode,
    input  logic [3:0]  numberPressedData,
    input  logic        numberPressed
);

  // Re-declare DUT parameters for readable checks
  localparam CHANNEL_MINUS = 8'hA2,
             CHANNEL       = 8'h62,
             CHANNEL_PLUS  = 8'hE2,
             PLAY          = 8'hC2,
             EQ            = 8'h90,
             N0=8'h68, N1=8'h30, N2=8'h18, N3=8'h7A, N4=8'h10,
             N5=8'h38, N6=8'h5A, N7=8'h42, N8=8'h4A, N9=8'h52;

  localparam IDLE         = 3'b000,
             LEADING_9MS  = 3'b001,
             LEADING_4MS  = 3'b010,
             DATA_READ    = 3'b100;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset values right after deassert
  assert property (@(posedge clk) $fell(rst) |-> (ir0==0 && ir1==0 && ir2==0 &&
                                                  counter1==0 && counter2==0 &&
                                                  state==IDLE &&
                                                  irDataPos==0 && irRead==32'b0 && err==0 &&
                                                  showName==0 && mode==0 && cpuClkMode==0 &&
                                                  numberPressed==0 && numberPressedData==0));

  // 3-stage sync and edge detection correctness
  assert property ($past(!rst) |-> (ir1 == $past(ir0)));
  assert property ($past(!rst) |-> (ir2 == $past(ir1)));
  assert property (irPosEdge == (ir1 && !$past(ir1)));
  assert property (irNegEdge == (!ir1 &&  $past(ir1)));
  assert property (irChange  == (ir1 ^   $past(ir1)));
  assert property (!(irPosEdge && irNegEdge));

  // counter1/2 behavior
  assert property ($past(!rst && irChange) |-> (counter1==0 && counter2==0));
  assert property ($past(!rst && !irChange && (counter1==11'd1750)) |-> (counter1==0));
  assert property ($past(!rst && !irChange && ($past(counter1)==11'd1750)) |-> (counter2 == $past(counter2)+1));
  assert property ($past(!rst && !irChange && ($past(counter1)!=11'd1750)) |-> (counter2 == $past(counter2)));
  assert property (counter1 <= 11'd1750);

  // Legal state encoding
  assert property (state inside {IDLE,LEADING_9MS,LEADING_4MS,DATA_READ});

  // FSM transition checks
  assert property ($past(state)==IDLE         && $past(ir1)                         |-> state==LEADING_9MS);
  assert property ($past(state)==IDLE         && !$past(ir1)                        |-> state==IDLE);

  assert property ($past(state)==LEADING_9MS  && $past(irNegEdge) &&  $past(check9ms) |-> state==LEADING_4MS);
  assert property ($past(state)==LEADING_9MS  && $past(irNegEdge) && !$past(check9ms) |-> state==IDLE);
  assert property ($past(state)==LEADING_9MS  && !$past(irNegEdge)                    |-> state==LEADING_9MS);

  assert property ($past(state)==LEADING_4MS  && $past(irPosEdge) &&  $past(check4ms) |-> state==DATA_READ);
  assert property ($past(state)==LEADING_4MS  && $past(irPosEdge) && !$past(check4ms) |-> state==IDLE);
  assert property ($past(state)==LEADING_4MS  && !$past(irPosEdge)                    |-> state==LEADING_4MS);

  assert property ($past(state)==DATA_READ && ($past(irDataPos)==6'd32) && !$past(ir1) && !$past(ir2) |-> state==IDLE);
  assert property ($past(state)==DATA_READ &&  $past(err)                                                    |-> state==IDLE);
  assert property ($past(state)==DATA_READ && !($past(err) || (($past(irDataPos)==6'd32) && !$past(ir1) && !$past(ir2))) |-> state==DATA_READ);

  // IDLE datapath clear
  assert property (state==IDLE |-> (irDataPos==0 && irRead==32'b0 && err==0));

  // DATA_READ data path checks
  assert property ($past(state)==DATA_READ && $past(irNegEdge) && !$past(high) |-> err==1);

  assert property ($past(state)==DATA_READ && $past(irPosEdge) |-> irRead[31:1] == $past(irRead[30:0]));
  assert property ($past(state)==DATA_READ && $past(irPosEdge) && $past(high)  |-> irRead[0]==1'b0);
  assert property ($past(state)==DATA_READ && $past(irPosEdge) && $past(low)   |-> irRead[0]==1'b1);
  assert property ($past(state)==DATA_READ && $past(irPosEdge) && !($past(high)||$past(low)) |-> err==1);

  assert property ($past(state)==DATA_READ && $past(irPosEdge) |-> irDataPos == $past(irDataPos)+1);
  assert property ($past(state)==DATA_READ && !$past(irPosEdge) |-> irDataPos == $past(irDataPos));

  // stateOut definition consistency
  assert property (stateOut == ((irDataPos==6'd32) && !ir2 && !ir1));

  // Command decode event (when outputs update)
  wire cmd_evt = (irDataPos==6'd32) && !ir1 && ir2;

  // CHANNEL: toggle showName
  assert property (cmd_evt && (irRead[15:8]==CHANNEL) |-> showName == ~$past(showName));

  // CHANNEL_PLUS/MINUS wrap behavior
  assert property (cmd_evt && (irRead[15:8]==CHANNEL_PLUS)
                   |-> mode == (($past(mode) < 4'd13) ? ($past(mode)+1) : 4'd0));
  assert property (cmd_evt && (irRead[15:8]==CHANNEL_MINUS)
                   |-> mode == (($past(mode) > 4'd0) ? ($past(mode)-1) : 4'd13));

  // PLAY/EQ toggle bits
  assert property (cmd_evt && (irRead[15:8]==PLAY) |-> cpuClkMode[1] == ~$past(cpuClkMode[1]) && cpuClkMode[0] == $past(cpuClkMode[0]));
  assert property (cmd_evt && (irRead[15:8]==EQ)   |-> cpuClkMode[0] == ~$past(cpuClkMode[0]) && cpuClkMode[1] == $past(cpuClkMode[1]));

  // Number decode and one-cycle pulse
  assert property (cmd_evt && (irRead[15:8]==N0) |-> numberPressed && numberPressedData==4'd0);
  assert property (cmd_evt && (irRead[15:8]==N1) |-> numberPressed && numberPressedData==4'd1);
  assert property (cmd_evt && (irRead[15:8]==N2) |-> numberPressed && numberPressedData==4'd2);
  assert property (cmd_evt && (irRead[15:8]==N3) |-> numberPressed && numberPressedData==4'd3);
  assert property (cmd_evt && (irRead[15:8]==N4) |-> numberPressed && numberPressedData==4'd4);
  assert property (cmd_evt && (irRead[15:8]==N5) |-> numberPressed && numberPressedData==4'd5);
  assert property (cmd_evt && (irRead[15:8]==N6) |-> numberPressed && numberPressedData==4'd6);
  assert property (cmd_evt && (irRead[15:8]==N7) |-> numberPressed && numberPressedData==4'd7);
  assert property (cmd_evt && (irRead[15:8]==N8) |-> numberPressed && numberPressedData==4'd8);
  assert property (cmd_evt && (irRead[15:8]==N9) |-> numberPressed && numberPressedData==4'd9);
  assert property ($past(cmd_evt && (irRead[15:8] inside {N0,N1,N2,N3,N4,N5,N6,N7,N8,N9})) |-> numberPressed==1'b0);
  assert property (cmd_evt && !(irRead[15:8] inside {N0,N1,N2,N3,N4,N5,N6,N7,N8,N9}) |-> numberPressed==1'b0);

  // Coverage: nominal frame, completion, errors, commands
  cover property ($rose(ir1) ##[1:200] (irNegEdge && check9ms) ##[1:200] (irPosEdge && check4ms) ##1 (state==DATA_READ));
  cover property (state==DATA_READ ##[1:5000] (irDataPos==6'd32 && !ir1 && ir2));
  cover property ($rose(err));

  cover property (cmd_evt && (irRead[15:8]==CHANNEL));
  cover property (cmd_evt && (irRead[15:8]==CHANNEL_PLUS));
  cover property (cmd_evt && (irRead[15:8]==CHANNEL_MINUS));
  cover property (cmd_evt && (irRead[15:8]==PLAY));
  cover property (cmd_evt && (irRead[15:8]==EQ));
  cover property (cmd_evt && (irRead[15:8] inside {N0,N1,N2,N3,N4,N5,N6,N7,N8,N9}));

endmodule

// Bind to all DebugIR instances
bind DebugIR DebugIR_sva dbgir_sva (.*);
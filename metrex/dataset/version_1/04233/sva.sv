// SVA for Key_Command_Controller
// Bind this checker to the DUT (bind snippet at bottom)

module Key_Command_Controller_sva (
  input  logic        CLK,
  input  logic        RESET,
  // key inputs
  input  logic        KEY_CLEAR,
  input  logic        KEY_ADD,
  input  logic        KEY_SUB,
  // command handshake
  input  logic        CMD_DONE,
  // DUT outputs
  input  logic        CMD_CLEAR,
  input  logic        CMD_COMPUTE,
  input  logic        CMD_OPERATION,
  // DUT internals
  input  logic [3:0]  State,
  input  logic [1:0]  key_reg
);

  // Mirror DUT encoding
  localparam logic [3:0] S0 = 4'b0001;
  localparam logic [3:0] S1 = 4'b0010;
  localparam logic [3:0] S2 = 4'b0100;
  localparam logic [3:0] S3 = 4'b1000;

  default clocking cb @(posedge CLK); endclocking

  // Asynchronous reset effect (checked even when RESET=1)
  assert property (@(posedge CLK)
    RESET |-> (State==S0 && key_reg==2'h0 &&
               !CMD_CLEAR && !CMD_COMPUTE && !CMD_OPERATION));

  // Basic state encoding/legality
  assert property (cb $onehot(State));

  // Key capture: when in S0, next-cycle key_reg mirrors inputs
  assert property (cb $past(State==S0) |-> key_reg==={$past(KEY_SUB),$past(KEY_ADD)});

  // State transitions out of S0
  assert property (cb $past(State==S0 && KEY_CLEAR) |-> State==S2);
  assert property (cb $past(State==S0 && !KEY_CLEAR && (KEY_ADD||KEY_SUB)) |-> State==S1);
  assert property (cb $past(State==S0 && !KEY_CLEAR && !(KEY_ADD||KEY_SUB)) |-> State==S0);

  // S2 behavior: one-cycle CMD_CLEAR pulse, then go to S3
  assert property (cb $past(State==S2) |-> $past(CMD_CLEAR) && !CMD_CLEAR && State==S3);
  // CMD_CLEAR never extends beyond 1 cycle
  assert property (cb $past(CMD_CLEAR) |-> !CMD_CLEAR);

  // S1 behavior: branch based on validity of captured key
  assert property (cb $past(State==S1) |-> State==( ^$past(key_reg) ? S3 : S0));

  // S1 valid: compute pulse exactly one cycle and operation matches key
  assert property (cb $past(State==S1) |-> ($past(CMD_COMPUTE)==^$past(key_reg)));
  assert property (cb $past(State==S1 && ^$past(key_reg)) |-> $past(CMD_OPERATION)==$past(key_reg[1]));
  // S1 invalid: no compute, default operation=0, return to S0
  assert property (cb $past(State==S1 && !^$past(key_reg)) |-> (!$past(CMD_COMPUTE) && $past(CMD_OPERATION)==1'b0 && State==S0));

  // Compute never extends beyond 1 cycle
  assert property (cb $past(CMD_COMPUTE) |-> !CMD_COMPUTE);

  // S3: outputs cleared and hold until CMD_DONE, then return to S0
  assert property (cb $past(State)==S3 |-> (!CMD_CLEAR && !CMD_COMPUTE));
  assert property (cb $past(State==S3 && !CMD_DONE) |-> State==S3);
  assert property (cb $past(State==S3 && CMD_DONE)  |-> State==S0);

  // Stability constraints
  assert property (cb (State!=S1) |-> $stable(CMD_OPERATION)); // only S1 updates operation
  assert property (cb (State!=S0) |-> $stable(key_reg));        // key_reg only updates in S0

  // Sanity: no outputs asserted in S0 unless just pulsed in prior cycle
  assert property (cb (State==S0) |-> (!CMD_CLEAR && !CMD_COMPUTE));

  // Coverage
  // Valid ADD flow
  cover property (cb State==S0 && !KEY_CLEAR && KEY_ADD && !KEY_SUB
                  ##1 $past(State)==S1 && ^$past(key_reg) && $past(CMD_COMPUTE)
                  ##1 $past(State)==S3 ##[1:$] $past(State)==S3 && CMD_DONE ##1 State==S0);
  // Valid SUB flow
  cover property (cb State==S0 && !KEY_CLEAR && !KEY_ADD && KEY_SUB
                  ##1 $past(State)==S1 && ^$past(key_reg) && $past(CMD_COMPUTE)
                  ##1 $past(State)==S3 ##[1:$] $past(State)==S3 && CMD_DONE ##1 State==S0);
  // CLEAR flow
  cover property (cb State==S0 && KEY_CLEAR
                  ##1 $past(State)==S2 && $past(CMD_CLEAR)
                  ##1 $past(State)==S3 ##[1:$] $past(State)==S3 && CMD_DONE ##1 State==S0);
  // Invalid (both keys) -> abort to S0
  cover property (cb State==S0 && !KEY_CLEAR && KEY_ADD && KEY_SUB
                  ##1 $past(State)==S1 && !$past(^key_reg) && !$past(CMD_COMPUTE)
                  ##1 State==S0);
  // S3 wait then done
  cover property (cb $past(State)==S3 && !CMD_DONE ##1 $past(State)==S3 && !CMD_DONE
                  ##1 $past(State)==S3 && CMD_DONE ##1 State==S0);

endmodule

// Bind example:
// bind Key_Command_Controller Key_Command_Controller_sva sva (
//   .CLK(CLK), .RESET(RESET),
//   .KEY_CLEAR(KEY_CLEAR), .KEY_ADD(KEY_ADD), .KEY_SUB(KEY_SUB),
//   .CMD_DONE(CMD_DONE),
//   .CMD_CLEAR(CMD_CLEAR), .CMD_COMPUTE(CMD_COMPUTE), .CMD_OPERATION(CMD_OPERATION),
//   .State(State), .key_reg(key_reg)
// );
// SVA for control_o
// Bindable, concise, with full state/output checking, transitions, reset, and coverage.

module control_o_sva
(
  input  logic        clk_2,
  input  logic        reset,
  input  logic        rxd,
  input  logic        StringReady,
  input  logic        CharReady,
  input  logic        parity,
  input  logic        check,

  input  logic        ready,
  input  logic        error,
  input  logic        WriteChar,
  input  logic        WriteString,
  input  logic        PossibleStart,

  input  logic [2:0]  current_state,
  input  logic [2:0]  next_state
);

  // State encodings (mirror DUT)
  localparam logic [2:0]
    IDLE          = 3'b000,
    POSSIBLESTART = 3'b001,
    READ          = 3'b010,
    ERROR_S       = 3'b011, // renamed local to avoid keyword collision
    WRITE         = 3'b100,
    STOP          = 3'b101;

  default clocking cb @(negedge clk_2); endclocking

  // While reset is asserted, state and outputs are forced
  assert property (cb reset |-> (current_state==IDLE
                                 && ready==0 && error==0
                                 && WriteChar==0 && WriteString==0 && PossibleStart==0));

  // State must always be legal when not in reset
  assert property (cb disable iff (reset)
                   (current_state inside {IDLE,POSSIBLESTART,READ,ERROR_S,WRITE,STOP}));

  // Output decode checks (Moore outputs + parity in ERROR)
  assert property (cb disable iff (reset) (current_state==IDLE)
                   |-> (ready==0 && error==0 && WriteChar==0 && WriteString==0 && PossibleStart==0));

  assert property (cb disable iff (reset) (current_state==POSSIBLESTART)
                   |-> (ready==0 && error==0 && WriteChar==0 && WriteString==0 && PossibleStart==1));

  assert property (cb disable iff (reset) (current_state==READ)
                   |-> (ready==0 && error==0 && WriteChar==1 && WriteString==0 && PossibleStart==0));

  assert property (cb disable iff (reset) (current_state==ERROR_S)
                   |-> (ready==0 && error==(parity) && WriteChar==0 && WriteString==0 && PossibleStart==0));

  assert property (cb disable iff (reset) (current_state==WRITE)
                   |-> (ready==0 && error==0 && WriteChar==0 && WriteString==1 && PossibleStart==0));

  assert property (cb disable iff (reset) (current_state==STOP)
                   |-> (ready==1 && error==0 && WriteChar==0 && WriteString==0 && PossibleStart==0));

  // At most one output high at a time
  assert property (cb disable iff (reset) $onehot0({ready,error,WriteChar,WriteString,PossibleStart}));

  // Sequential state transition checks (registered state)
  assert property (cb disable iff (reset) (current_state==IDLE && rxd==1)  |-> ##1 (current_state==IDLE));
  assert property (cb disable iff (reset) (current_state==IDLE && rxd==0)  |-> ##1 (current_state==POSSIBLESTART));

  assert property (cb disable iff (reset) (current_state==POSSIBLESTART && !check)           |-> ##1 (current_state==POSSIBLESTART));
  assert property (cb disable iff (reset) (current_state==POSSIBLESTART && check && rxd==0)  |-> ##1 (current_state==READ));
  assert property (cb disable iff (reset) (current_state==POSSIBLESTART && check && rxd==1)  |-> ##1 (current_state==IDLE));

  assert property (cb disable iff (reset) (current_state==READ && CharReady==0)  |-> ##1 (current_state==READ));
  assert property (cb disable iff (reset) (current_state==READ && CharReady==1)  |-> ##1 (current_state==ERROR_S));

  assert property (cb disable iff (reset) (current_state==ERROR_S) |-> ##1 (current_state==WRITE));

  assert property (cb disable iff (reset) (current_state==WRITE && StringReady==0) |-> ##1 (current_state==IDLE));
  assert property (cb disable iff (reset) (current_state==WRITE && StringReady==1) |-> ##1 (current_state==STOP));

  assert property (cb disable iff (reset) (current_state==STOP) |-> ##1 (current_state==IDLE));

  // Combinational next_state decode checks (immediate next_state function)
  assert property (cb disable iff (reset) (current_state==IDLE)
                   |-> (next_state == (rxd ? IDLE : POSSIBLESTART)));

  assert property (cb disable iff (reset) (current_state==POSSIBLESTART && !check)
                   |-> (next_state == POSSIBLESTART));
  assert property (cb disable iff (reset) (current_state==POSSIBLESTART && check && (rxd==0))
                   |-> (next_state == READ));
  assert property (cb disable iff (reset) (current_state==POSSIBLESTART && check && (rxd==1))
                   |-> (next_state == IDLE));

  assert property (cb disable iff (reset) (current_state==READ)
                   |-> (next_state == (CharReady ? ERROR_S : READ)));

  assert property (cb disable iff (reset) (current_state==ERROR_S)
                   |-> (next_state == WRITE));

  assert property (cb disable iff (reset) (current_state==WRITE)
                   |-> (next_state == (StringReady ? STOP : IDLE)));

  assert property (cb disable iff (reset) (current_state==STOP)
                   |-> (next_state == IDLE));

  // Functional coverage
  cover property (cb disable iff (reset)
    (current_state==IDLE && rxd==0)
    ##1 (current_state==POSSIBLESTART && check==1 && rxd==0)
    ##1 (current_state==READ && CharReady==1)
    ##1 (current_state==ERROR_S && parity==1)
    ##1 (current_state==WRITE && StringReady==1)
    ##1 (current_state==STOP)
    ##1 (current_state==IDLE)
  );

  cover property (cb disable iff (reset)
    (current_state==IDLE && rxd==0)
    ##1 (current_state==POSSIBLESTART && check==1 && rxd==0)
    ##1 (current_state==READ && CharReady==1)
    ##1 (current_state==ERROR_S && parity==0)
    ##1 (current_state==WRITE && StringReady==0)
    ##1 (current_state==IDLE)
  );

  cover property (cb disable iff (reset)
    (current_state==POSSIBLESTART && check==0)[*2] ##1 (current_state==POSSIBLESTART && check==1 && rxd==1) ##1 (current_state==IDLE)
  );

  cover property (cb disable iff (reset)
    (current_state==READ && CharReady==0)[*2] ##1 (current_state==READ && CharReady==1) ##1 (current_state==ERROR_S)
  );

  // State hit coverage
  cover property (cb disable iff (reset) current_state==IDLE);
  cover property (cb disable iff (reset) current_state==POSSIBLESTART);
  cover property (cb disable iff (reset) current_state==READ);
  cover property (cb disable iff (reset) current_state==ERROR_S);
  cover property (cb disable iff (reset) current_state==WRITE);
  cover property (cb disable iff (reset) current_state==STOP);

endmodule

// Bind into DUT
bind control_o control_o_sva sva (
  .clk_2(clk_2),
  .reset(reset),
  .rxd(rxd),
  .StringReady(StringReady),
  .CharReady(CharReady),
  .parity(parity),
  .check(check),

  .ready(ready),
  .error(error),
  .WriteChar(WriteChar),
  .WriteString(WriteString),
  .PossibleStart(PossibleStart),

  .current_state(current_state),
  .next_state(next_state)
);
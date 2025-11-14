// SVA for ChannelArbiter
// Bind this file to the DUT:  bind ChannelArbiter ChannelArbiter_sva u_arb_sva();

module ChannelArbiter_sva;

  // Re-declare state encodings (match DUT)
  localparam State_Idle    = 5'b00001;
  localparam State_Select  = 5'b00010;
  localparam State_Out     = 5'b00100;
  localparam State_Dummy   = 5'b01000;
  localparam State_Standby = 5'b10000;

  default clocking cb @ (posedge iClock); endclocking
  default disable iff (iReset);

  // ------------------------
  // Reset and invariants
  // ------------------------
  // On reset
  assert property (@(posedge iClock)
    iReset |-> (rCurState==State_Idle
                && rKESAvail==4'b0000
                && rChannelNumber==2'b00
                && rPriorityQ0==4'b0001
                && rPriorityQ1==4'b0010
                && rPriorityQ2==4'b0100
                && rPriorityQ3==4'b1000));

  // State is one-hot
  assert property ($onehot(rCurState));

  // Priority queues are each one-hot and form a permutation of 4'b1111
  assert property ($onehot(rPriorityQ0) && $onehot(rPriorityQ1)
                   && $onehot(rPriorityQ2) && $onehot(rPriorityQ3)
                   && ((rPriorityQ0 | rPriorityQ1 | rPriorityQ2 | rPriorityQ3) == 4'b1111));

  // rKESAvail is onehot0 (0 or one-hot)
  assert property ($onehot0(rKESAvail));

  // Channel number is directly wired to output
  assert property (oChannelNumber == rChannelNumber);

  // ------------------------
  // FSM transition correctness
  // ------------------------
  // Idle transitions
  assert property (rCurState==State_Idle && (|iRequestChannel && iKESAvail) |=> rCurState==State_Select);
  assert property (rCurState==State_Idle && !(|iRequestChannel && iKESAvail) |=> rCurState==State_Idle);

  // Deterministic steps
  assert property (rCurState==State_Select |=> rCurState==State_Out);
  assert property (rCurState==State_Out    |=> rCurState==State_Dummy);

  // Dummy branches
  assert property (rCurState==State_Dummy &&  iLastChunk[rChannelNumber]  |=> rCurState==State_Idle);
  assert property (rCurState==State_Dummy && !iLastChunk[rChannelNumber]  |=> rCurState==State_Standby);

  // Standby branches
  assert property (rCurState==State_Standby &&  iKESAvail |=> rCurState==State_Out);
  assert property (rCurState==State_Standby && !iKESAvail |=> rCurState==State_Standby);

  // ------------------------
  // Outputs/gating
  // ------------------------
  // oKESAvail only valid in State_Out and equals rKESAvail; zero otherwise
  assert property ( (rCurState==State_Out)  |-> (oKESAvail == rKESAvail && oKESAvail!=4'b0 && $onehot(oKESAvail)) );
  assert property ( (rCurState!=State_Out)  |-> (oKESAvail == 4'b0) );

  // ------------------------
  // Register update protocol (since DUT updates by rNextState)
  // ------------------------
  // rKESAvail forced to zero when next state is Idle
  assert property ($past(rNextState)==State_Idle |-> rKESAvail==4'b0000);

  // rKESAvail only changes on Select or Idle; otherwise holds
  assert property (!($past(rNextState) inside {State_Select,State_Idle}) |-> rKESAvail==$past(rKESAvail));

  // rChannelNumber only changes on Select; otherwise holds
  assert property ($past(rNextState)!=State_Select |-> rChannelNumber==$past(rChannelNumber));

  // Selection semantics and priority order resolution
  assert property ( $past(rNextState)==State_Select |-> 
                    ( $past(|(iRequestChannel & rPriorityQ0)) ? (rKESAvail==$past(rPriorityQ0)) :
                      $past(|(iRequestChannel & rPriorityQ1)) ? (rKESAvail==$past(rPriorityQ1)) :
                      $past(|(iRequestChannel & rPriorityQ2)) ? (rKESAvail==$past(rPriorityQ2)) :
                      $past(|(iRequestChannel & rPriorityQ3)) ? (rKESAvail==$past(rPriorityQ3)) :
                      (rKESAvail==$past(rKESAvail)) ) );

  // Channel encoding matches selected one-hot whenever rKESAvail != 0
  assert property ( (rKESAvail==4'b0001) |-> (rChannelNumber==2'd0) );
  assert property ( (rKESAvail==4'b0010) |-> (rChannelNumber==2'd1) );
  assert property ( (rKESAvail==4'b0100) |-> (rChannelNumber==2'd2) );
  assert property ( (rKESAvail==4'b1000) |-> (rChannelNumber==2'd3) );

  // ------------------------
  // Functional coverage
  // ------------------------
  // Cover all main paths
  cover property (rCurState==State_Idle ##1 rCurState==State_Select ##1 rCurState==State_Out ##1 rCurState==State_Dummy ##1 rCurState==State_Idle);
  cover property (rCurState==State_Idle ##1 rCurState==State_Select ##1 rCurState==State_Out ##1 rCurState==State_Dummy ##1 rCurState==State_Standby ##1 rCurState==State_Out);

  // Cover each channel getting granted (visible in Out)
  cover property (rCurState==State_Out && oKESAvail==4'b0001);
  cover property (rCurState==State_Out && oKESAvail==4'b0010);
  cover property (rCurState==State_Out && oKESAvail==4'b0100);
  cover property (rCurState==State_Out && oKESAvail==4'b1000);

endmodule

bind ChannelArbiter ChannelArbiter_sva u_arb_sva();
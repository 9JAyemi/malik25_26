// SVA for NegClockedOneShot
// Bind these checkers to the DUT

module NegClockedOneShot_sva
  #(parameter State0=0, State1=1, State2=2)
  (input  logic        CLOCK,
   input  logic        Reset,
   input  logic        InputPulse,
   input  logic [7:0]  Time,
   input  logic        OneShot,
   input  logic [1:0]  State,
   input  logic [7:0]  Counter);

  default clocking cb @(posedge CLOCK); endclocking

  // Basic sanity
  assert property (cb State inside {State0,State1,State2});

  // Synchronous reset effects
  assert property (cb Reset |=> (State==State0 && Counter==8'd0));

  // Invariants in State0/State2
  assert property (cb (State==State0) |-> (Counter==8'd0));
  assert property (cb (State==State2) |-> (Counter==8'd0));

  // Transitions out of State0
  assert property (cb disable iff (Reset)
                   (State==State0 && InputPulse==1'b0) |=> (State==State0 && Counter==8'd0));
  assert property (cb disable iff (Reset)
                   (State==State0 && InputPulse==1'b1) |=> (State==State1 && Counter==8'd0));

  // State1 counting and exit
  assert property (cb disable iff (Reset)
                   (State==State1 && (Counter < Time)) |=> (State==State1 && Counter == $past(Counter)+8'd1));
  assert property (cb disable iff (Reset)
                   (State==State1 && !(Counter < Time)) |=> (State==State2 && Counter==8'd0));

  // State2 -> State0
  assert property (cb disable iff (Reset)
                   (State==State2) |=> (State==State0 && Counter==8'd0));

  // OneShot behavior at negedge InputPulse
  assert property (@(negedge InputPulse) OneShot == ((Reset==1'b0) && (State==State1)));

  // Coverage

  // Typical path: idle -> detect pulse -> count -> done -> idle
  cover property (cb disable iff (Reset)
    (State==State0 && InputPulse) ##1
    (State==State1 && (Counter < Time)) [*1:$] ##1
    (State==State2) ##1
    (State==State0));

  // Time==0 corner: immediate exit from State1 next cycle
  cover property (cb disable iff (Reset)
    (State==State0 && InputPulse && Time==8'd0) ##1
    (State==State1) ##1
    (State==State2) ##1
    (State==State0));

  // OneShot asserted only when negedge occurs in State1 without Reset
  cover property (@(negedge InputPulse) (Reset==1'b0 && State==State1) && OneShot);

  // OneShot deasserted when negedge occurs outside State1
  cover property (@(negedge InputPulse) (Reset==1'b0 && State!=State1) && !OneShot);

  // OneShot cleared on negedge when Reset is 1
  cover property (@(negedge InputPulse) (Reset==1'b1) && !OneShot);

endmodule

bind NegClockedOneShot
  NegClockedOneShot_sva #(.State0(State0), .State1(State1), .State2(State2)) i_NegClockedOneShot_sva (
    .CLOCK(CLOCK),
    .Reset(Reset),
    .InputPulse(InputPulse),
    .Time(Time),
    .OneShot(OneShot),
    .State(State),
    .Counter(Counter)
  );
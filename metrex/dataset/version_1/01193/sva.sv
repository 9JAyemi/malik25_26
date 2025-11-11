// SVA checker for mealy_fsm
// Bind this to the DUT to verify functional correctness and provide concise coverage.

module mealy_fsm_sva #(
  parameter A = 2'b00,
  parameter B = 2'b01,
  parameter C = 2'b10,
  parameter D = 2'b11
)(
  input  logic       clk,
  input  logic       reset,
  input  logic       in1,
  input  logic       in2,
  input  logic       out,
  input  logic [1:0] state,
  input  logic [1:0] next_state
);

  // Basic static sanity on encodings (compile-time/initial-time)
  initial begin
    assert (A!=B && A!=C && A!=D && B!=C && B!=D && C!=D)
      else $error("State encodings must be distinct");
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // No X/Z on key signals (at sample)
  assert property (!$isunknown({state,next_state,out})))
    else $error("X/Z detected on state/next_state/out");
  assert property (!$isunknown({in1,in2})))
    else $error("X/Z detected on inputs");

  // State is always one of the defined encodings
  assert property (state inside {A,B,C,D})
    else $error("Illegal state value");
  assert property (next_state inside {A,B,C,D})
    else $error("Illegal next_state value");

  // Reset behavior (checked with reset in effect)
  assert property (@(posedge clk) reset |=> state == A)
    else $error("State not A after reset");

  // Sequential update: state follows next_state when not in reset
  assert property (state == $past(next_state))
    else $error("State does not follow next_state");

  // Mealy mapping: next_state and out as a function of current state and inputs
  // 11 -> D, out=0 (from any state)
  assert property ((in1 && in2) |-> (next_state == D && out == 1'b0))
    else $error("Mapping error on in1,in2=11");

  // 10 -> C, out=1
  assert property ((in1 && !in2) |-> (next_state == C && out == 1'b1))
    else $error("Mapping error on in1,in2=10");

  // 01 -> B, out=0
  assert property ((!in1 && in2) |-> (next_state == B && out == 1'b0))
    else $error("Mapping error on in1,in2=01");

  // 00 -> hold state; out=1 only if state==C, else 0
  assert property ((!in1 && !in2) |-> (next_state == state && out == (state==C)))
    else $error("Mapping error on in1,in2=00");

  // With 00 inputs, state holds across the clock
  assert property ((!in1 && !in2) |=> $stable(state))
    else $error("State not stable on 00 inputs");

  // Concise functional coverage
  cover property (state==A);
  cover property (state==B);
  cover property (state==C);
  cover property (state==D);

  cover property ((in1 && in2) ##0 (next_state==D && out==0));
  cover property ((in1 && !in2) ##0 (next_state==C && out==1));
  cover property ((!in1 && in2) ##0 (next_state==B && out==0));
  cover property ((state==C && !in1 && !in2 && out==1) ##1 state==C);

endmodule

// Example bind (place in a separate file or a package included after DUT declaration):
// bind mealy_fsm mealy_fsm_sva #(.A(A),.B(B),.C(C),.D(D))
//   mealy_fsm_sva_i ( .clk(clk), .reset(reset), .in1(in1), .in2(in2),
//                     .out(out), .state(state), .next_state(next_state) );
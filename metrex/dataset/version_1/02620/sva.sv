// SVA for handshake module
// Bind-friendly checker that uses internal state/error
module handshake_sva
(
  input logic        clk,
  input logic        req,
  input logic        ack,
  input logic        reset,
  input logic [2:0]  state,
  input logic        error
);
  default clocking cb @(posedge clk); endclocking

  localparam logic [2:0]
    S_IDLE = 3'b000,
    S_REQ  = 3'b001,
    S_RA   = 3'b010,
    S_ACK  = 3'b011,
    S_ERR  = 3'b100;

  // Error/state consistency
  assert property (state == S_ERR |-> error);
  assert property (error |-> state == S_ERR);
  assert property ((state inside {S_IDLE,S_REQ,S_RA,S_ACK}) |-> !error);

  // S_IDLE transitions
  assert property (state==S_IDLE && !req && !ack |=> state==S_IDLE && !error);
  assert property (state==S_IDLE &&  req && !ack |=> state==S_REQ  && !error);
  assert property (state==S_IDLE &&  ack            |=> state==S_ERR && error);

  // S_REQ transitions (allowed: 10 hold, 11 -> RA; any !req -> ERR)
  assert property (state==S_REQ &&  req && !ack |=> state==S_REQ && !error);
  assert property (state==S_REQ &&  req &&  ack |=> state==S_RA  && !error);
  assert property (state==S_REQ && !req         |=> state==S_ERR && error);

  // S_RA transitions (allowed: 11 hold, 01 -> ACK; any !ack -> ERR)
  assert property (state==S_RA &&  req &&  ack |=> state==S_RA  && !error);
  assert property (state==S_RA && !req &&  ack |=> state==S_ACK && !error);
  assert property (state==S_RA &&        !ack |=> state==S_ERR && error);

  // S_ACK transitions (allowed: 01 hold, 00 -> IDLE; any req -> ERR)
  assert property (state==S_ACK && !req &&  ack |=> state==S_ACK && !error);
  assert property (state==S_ACK && !req && !ack |=> state==S_IDLE && !error);
  assert property (state==S_ACK &&  req         |=> state==S_ERR && error);

  // S_ERR behavior: sticky until reset; reset recovers to IDLE and clears error
  assert property (state==S_ERR && !reset |=> state==S_ERR && error);
  assert property (state==S_ERR &&  reset |=> state==S_IDLE && !error);

  // Optional: state encoding recovery if an illegal code ever appears
  assert property (!(state inside {S_IDLE,S_REQ,S_RA,S_ACK,S_ERR}) |=> state==S_ERR && error);

  // Coverage
  cover property (state==S_IDLE ##1 state==S_REQ ##1 state==S_RA ##1 state==S_ACK ##1 state==S_IDLE);
  cover property (state==S_IDLE && ack |=> state==S_ERR);     // illegal ack in IDLE triggers error
  cover property (state==S_ERR  && reset |=> state==S_IDLE);  // recovery via reset
  cover property (state==S_IDLE);
  cover property (state==S_REQ);
  cover property (state==S_RA);
  cover property (state==S_ACK);
  cover property (state==S_ERR);
endmodule

// Bind into DUT (place in a package or a separate SV file)
// bind handshake handshake_sva hsva(.clk(clk), .req(req), .ack(ack), .reset(reset), .state(state), .error(error));
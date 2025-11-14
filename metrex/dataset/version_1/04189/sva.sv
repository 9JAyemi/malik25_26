// SVA for OneCycleStall
// Bind module to check internal state and I/O behavior

module OneCycleStall_sva (
  input logic        clk,
  input logic        resetn,
  input logic        request,
  input logic        stalled,
  input logic [1:0]  state
);

  default clocking cb @(posedge clk); endclocking

  // Basic reset behavior
  assert property (!resetn |-> (state == 2'b00 && stalled == 1'b0));

  // Known/valid values and legal states
  assert property (!$isunknown({state, stalled}));
  assert property (disable iff (!resetn) (state inside {2'b00,2'b01,2'b10}));

  // Output decode correctness
  assert property (stalled == (state == 2'b01));

  // FSM transitions
  assert property (disable iff (!resetn) (state==2'b00 &&  request) |=> (state==2'b01));
  assert property (disable iff (!resetn) (state==2'b00 && !request) |=> (state==2'b00));
  assert property (disable iff (!resetn) (state==2'b01)             |=> (state==2'b10));
  assert property (disable iff (!resetn) (state==2'b10)             |=> (state==2'b00));

  // Stall pulse is exactly one cycle wide
  assert property (disable iff (!resetn) $rose(stalled) |=> !stalled);

  // Stall (state==01) must be caused by an idle+request in prior cycle
  assert property (disable iff (!resetn) (state==2'b01) |-> $past(state==2'b00 && request));

  // Coverage
  cover property (disable iff (!resetn)
                  (state==2'b00 && request)
                  ##1 (state==2'b01)
                  ##1 (state==2'b10)
                  ##1 (state==2'b00));

  // Back-to-back requests with minimum gap (request held high)
  cover property (disable iff (!resetn)
                  (state==2'b00 && request)
                  ##1 (state==2'b01)
                  ##1 (state==2'b10)
                  ##1 (state==2'b00 && request)
                  ##1 (state==2'b01));

  // Requests while busy are ignored until returning to idle
  cover property (disable iff (!resetn)
                  (state==2'b01 && request)
                  ##1 (state==2'b10 && request)
                  ##1 (state==2'b00 && request)
                  ##1 (state==2'b01));

  // Immediate acceptance after reset deassert
  cover property ((!resetn) ##1 (resetn && request) ##1 (state==2'b01));

endmodule

// Bind to DUT (access internal state)
bind OneCycleStall OneCycleStall_sva u_OneCycleStall_sva (
  .clk    (clk),
  .resetn (resetn),
  .request(request),
  .stalled(stalled),
  .state  (state)
);
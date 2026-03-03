// SVA checker for state_machine
module sm_sva
  #(parameter logic [2:0] IDLE    = 3'b000,
                          SEND    = 3'b001,
                          WAIT1   = 3'b010,
                          UPDATE1 = 3'b011,
                          WAIT2   = 3'b100,
                          UPDATE2 = 3'b101)
(
  input  logic        clk,
  input  logic        rst_,
  input  logic [2:0]  state_r
);

  function automatic bit legal_state (logic [2:0] s);
    case (s)
      IDLE, SEND, WAIT1, UPDATE1, WAIT2, UPDATE2: return 1'b1;
      default: return 1'b0;
    endcase
  endfunction

  // Sanity
  assert property (@(posedge clk) !$isunknown(rst_));
  assert property (@(posedge clk) disable iff (!rst_) !$isunknown(state_r));
  assert property (@(posedge clk) disable iff (!rst_) legal_state(state_r));

  // Reset behavior
  assert property (@(posedge clk) (!rst_) |-> (state_r == IDLE));
  assert property (@(posedge clk) $fell(rst_) |=> (state_r == IDLE));
  assert property (@(posedge clk) $rose(rst_) |=> (state_r == IDLE) ##1 (state_r == SEND));

  // One-step transition helper
  property p_step (logic [2:0] from, logic [2:0] to);
    @(posedge clk) disable iff (!rst_) (state_r == from) |=> (state_r == to);
  endproperty

  // Legal transitions
  assert property (p_step(IDLE,    SEND));
  assert property (p_step(SEND,    WAIT1));
  assert property (p_step(WAIT1,   UPDATE1));
  assert property (p_step(UPDATE1, WAIT2));
  assert property (p_step(WAIT2,   UPDATE2));
  assert property (p_step(UPDATE2, IDLE));

  // Recovery from illegal encodings (should be vacuous)
  assert property (@(posedge clk) disable iff (!rst_)
                   (!legal_state(state_r)) |=> (state_r == IDLE));

  // End-to-end 6-step cycle from IDLE
  assert property (@(posedge clk) disable iff (!rst_)
                   (state_r == IDLE)
                   |-> ##1 (state_r == SEND)
                   ##1 (state_r == WAIT1)
                   ##1 (state_r == UPDATE1)
                   ##1 (state_r == WAIT2)
                   ##1 (state_r == UPDATE2)
                   ##1 (state_r == IDLE));

  // Coverage
  cover property (@(posedge clk) disable iff (!rst_)
                  (state_r == IDLE)
                  ##1 (state_r == SEND)
                  ##1 (state_r == WAIT1)
                  ##1 (state_r == UPDATE1)
                  ##1 (state_r == WAIT2)
                  ##1 (state_r == UPDATE2)
                  ##1 (state_r == IDLE));

  cover property (@(posedge clk) disable iff (!rst_) state_r == IDLE);
  cover property (@(posedge clk) disable iff (!rst_) state_r == SEND);
  cover property (@(posedge clk) disable iff (!rst_) state_r == WAIT1);
  cover property (@(posedge clk) disable iff (!rst_) state_r == UPDATE1);
  cover property (@(posedge clk) disable iff (!rst_) state_r == WAIT2);
  cover property (@(posedge clk) disable iff (!rst_) state_r == UPDATE2);

endmodule

// Bind into the DUT
bind state_machine sm_sva u_sm_sva (.*);
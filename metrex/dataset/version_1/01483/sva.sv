// SVA checker for TurnSignal. Bind to the DUT to verify state machine, outputs, and coverage.

module TurnSignal_sva #(
  parameter bit [2:0] ST_IDLE = 3'b000,
                      ST_L1   = 3'b001,
                      ST_L2   = 3'b010,
                      ST_L3   = 3'b011,
                      ST_R1   = 3'b100,
                      ST_R2   = 3'b101,
                      ST_R3   = 3'b110
)(
  input  logic        clk, reset, left, right,
  input  logic        LA, LB, LC, RA, RB, RC,
  input  logic [2:0]  state, next_state
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [2:0] f_next(input logic [2:0] s, input logic l, r);
    if (l && r) return ST_IDLE;
    unique case (s)
      ST_IDLE: begin
        if (l && !r) return ST_L1;
        else if (!l && r) return ST_R1;
        else return ST_IDLE;
      end
      ST_L1: return ST_L2;
      ST_L2: return ST_L3;
      ST_R1: return ST_R2;
      ST_R2: return ST_R3;
      default: return ST_IDLE; // includes L3/R3
    endcase
  endfunction

  // Reset behavior
  a_reset_idle: assert property (@cb reset |-> state == ST_IDLE);

  // Known/valid checks
  a_known:       assert property (@cb disable iff (reset) !$isunknown({state,next_state,LA,LB,LC,RA,RB,RC,left,right}));
  a_state_valid: assert property (@cb disable iff (reset) state inside {ST_IDLE,ST_L1,ST_L2,ST_L3,ST_R1,ST_R2,ST_R3});

  // Combinational next_state matches spec
  a_next_comb: assert property (@cb disable iff (reset) next_state == f_next(state,left,right));

  // Registered update implements one-cycle delayed f_next
  a_update: assert property (@cb disable iff (reset)
                             state == f_next($past(state), $past(left), $past(right)));

  // Both inputs high always force IDLE next cycle
  a_lr_abort: assert property (@cb disable iff (reset) (left && right) |=> state == ST_IDLE);

  // Output decode equivalence
  a_LA: assert property (@cb disable iff (reset) LA == (state inside {ST_L1,ST_L2,ST_L3}));
  a_LB: assert property (@cb disable iff (reset) LB == (state inside {ST_L2,ST_L3}));
  a_LC: assert property (@cb disable iff (reset) LC == (state inside {ST_L3}));
  a_RA: assert property (@cb disable iff (reset) RA == (state inside {ST_R1,ST_R2,ST_R3}));
  a_RB: assert property (@cb disable iff (reset) RB == (state inside {ST_R2,ST_R3}));
  a_RC: assert property (@cb disable iff (reset) RC == (state inside {ST_R3}));

  // Left vs right outputs never overlap
  a_left_right_excl: assert property (@cb disable iff (reset) !((LA|LB|LC) && (RA|RB|RC)));

  // Coverage
  c_each_state: cover property (@cb state inside {ST_IDLE,ST_L1,ST_L2,ST_L3,ST_R1,ST_R2,ST_R3});
  c_left_seq:   cover property (@cb state==ST_IDLE && left && !right
                                ##1 state==ST_L1 ##1 state==ST_L2 ##1 state==ST_L3 ##1 state==ST_IDLE);
  c_right_seq:  cover property (@cb state==ST_IDLE && right && !left
                                ##1 state==ST_R1 ##1 state==ST_R2 ##1 state==ST_R3 ##1 state==ST_IDLE);
  c_abort_mid:  cover property (@cb (state inside {ST_L1,ST_L2,ST_L3,ST_R1,ST_R2,ST_R3}) ##0 (left&&right)
                                ##1 state==ST_IDLE);
  c_both_idle:  cover property (@cb state==ST_IDLE && left&&right ##1 state==ST_IDLE);

endmodule

bind TurnSignal TurnSignal_sva #(
  .ST_IDLE(ST_IDLE), .ST_L1(ST_L1), .ST_L2(ST_L2), .ST_L3(ST_L3),
  .ST_R1(ST_R1), .ST_R2(ST_R2), .ST_R3(ST_R3)
) turnsignal_sva_i (
  .clk(clk), .reset(reset), .left(left), .right(right),
  .LA(LA), .LB(LB), .LC(LC), .RA(RA), .RB(RB), .RC(RC),
  .state(state), .next_state(next_state)
);
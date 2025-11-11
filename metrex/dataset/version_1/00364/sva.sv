// SVA checker for booth_multiplier
// Bind this module to the DUT to verify state machine, data-path updates,
// progress, and end-to-end correctness.

module booth_multiplier_sva #(
  parameter bit ASSUME_STABLE_INPUTS = 1
) (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [7:0]  P,
  input  logic [4:0]  m,
  input  logic [4:0]  ac,
  input  logic [2:0]  state
);

  default clocking cb @(posedge clk); endclocking
  // Helper
  function automatic bit in_busy(input logic [2:0] s);
    return (s != 3'b000);
  endfunction

  // Basic reset behavior
  assert property (reset |-> (m==5'b0 && ac==5'b0 && state==3'b000 && P==8'b0));
  assert property ($fell(reset) |-> state==3'b000);

  // Legal state encoding only
  assert property (!reset |-> state inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101});

  // FSM next-state transitions
  assert property (!reset && state==3'b000 |=> state==3'b001);
  assert property (!reset && state==3'b001 |=> state==3'b010);
  assert property (!reset && state==3'b010 |=> state==3'b011);
  assert property (!reset && state==3'b011 && (m==5'b00001 || m==5'b11111) |=> state==3'b100);
  assert property (!reset && state==3'b011 && !(m==5'b00001 || m==5'b11111) |=> state==3'b001);
  assert property (!reset && state==3'b100 |=> state==3'b101);
  assert property (!reset && state==3'b101 |=> state==3'b000);

  // m updates
  assert property (!reset && state==3'b000 |=> m == {B[3:1], 2'b01});
  assert property (!reset && state inside {3'b001,3'b010,3'b011} |=> m == {$past(m[3:1]), $past(m[0])});
  assert property (!reset && state inside {3'b100,3'b101} |=> m == $past(m));

  // ac updates
  // state 000: only when B[0]==1, load {0,A}; else hold
  assert property (!reset && state==3'b000 && B[0] |=> ac == {4'b0, $past(A)});
  assert property (!reset && state==3'b000 && !B[0] |=> ac == $past(ac));

  // states 001/010: add/sub per Booth bit-pair; otherwise hold
  assert property (!reset && state inside {3'b001,3'b010} && m[0] && !m[1]
                   |=> ac == $past(ac) + {4'b0, $past(A)});
  assert property (!reset && state inside {3'b001,3'b010} && !m[0] && m[1]
                   |=> ac == $past(ac) - {4'b0, $past(A)});
  assert property (!reset && state inside {3'b001,3'b010} && (m[0]==m[1])
                   |=> ac == $past(ac));

  // In states 011/100/101 ac must hold
  assert property (!reset && state inside {3'b011,3'b100,3'b101} |=> ac == $past(ac));

  // P updates
  // state 000: conditional init
  assert property (!reset && state==3'b000 && B[0] |=> P == {4'b0, $past(A)});
  assert property (!reset && state==3'b000 && !B[0] |=> P == 8'b0);

  // states 001/010: hold
  assert property (!reset && state inside {3'b001,3'b010} |=> P == $past(P));

  // states 011/100: shift/concat of ac and lower P nybble
  assert property (!reset && state==3'b011 |=> P == { $past(ac[4:0]), $past(P[3:0]) });
  assert property (!reset && state==3'b100 |=> P == { $past(ac[4:0]), $past(P[3:0]) });

  // state 101: hold
  assert property (!reset && state==3'b101 |=> P == $past(P));

  // No X/Z on key regs after reset deasserted
  assert property (!reset |-> !$isunknown({state,m,ac,P}));

  // Progress: from state 000 must reach 101 within 5..8 cycles
  assert property (!reset && state==3'b000 |=> ##[5:8] state==3'b101);

  // End-to-end functional check (unsigned product)
  property prod_correct;
    bit [3:0] a0,b0;
    (!reset && state==3'b000, a0=A, b0=B)
      |-> ##[5:8] (state==3'b101 && P == (a0*b0));
  endproperty
  assert property (prod_correct);

  // Assume: A,B stable during busy (optional, param-controlled)
  generate if (ASSUME_STABLE_INPUTS) begin
    assume property (!reset && in_busy(state) |-> $stable({A,B}));
  end endgenerate

  // Functional coverage
  // Complete multiply observed with correct result
  cover property (prod_correct);

  // Exercise both add and subtract cases (not necessarily same transaction)
  cover property (!reset && state inside {3'b001,3'b010} && m[0] && !m[1]);
  cover property (!reset && state inside {3'b001,3'b010} && !m[0] && m[1]);

  // Early-exit decision in state 3
  cover property (!reset && state==3'b011 && (m==5'b00001 || m==5'b11111));

  // Both init paths in state 0
  cover property (!reset && state==3'b000 && B[0]==1'b0);
  cover property (!reset && state==3'b000 && B[0]==1'b1);

endmodule

// Bind to DUT instance(s)
bind booth_multiplier booth_multiplier_sva #(.ASSUME_STABLE_INPUTS(1))
  booth_multiplier_sva_i (
    .clk   (clk),
    .reset (reset),
    .A     (A),
    .B     (B),
    .P     (P),
    .m     (m),
    .ac    (ac),
    .state (state)
  );
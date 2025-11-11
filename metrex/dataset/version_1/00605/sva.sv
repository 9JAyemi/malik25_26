// SVA for sky130_fd_sc_ms__a21boi_4
// Function: Y = (A1 & A2) | (~B1_N)

module sky130_fd_sc_ms__a21boi_4_sva (
  input logic Y,
  input logic A1,
  input logic A2,
  input logic B1_N
);

  // Sample on any input edge; check after ##0 to see settled Y
  // Functional equivalence when inputs are known; also enforces Y not X/Z then
  property p_func;
    @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
      !$isunknown({A1,A2,B1_N}) |-> ##0 (! $isunknown(Y) && (Y === ((A1 & A2) | (~B1_N))));
  endproperty
  assert property (p_func);

  // Dominance properties that hold even with Xs on the other inputs
  // B1_N low forces Y high
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                   (B1_N === 1'b0) |-> ##0 (Y === 1'b1));
  // A1&A2 high forces Y high
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                   (A1 === 1'b1 && A2 === 1'b1) |-> ##0 (Y === 1'b1));

  // Coverage: all 8 input combinations (after settle)
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b000));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b001));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b010));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b011));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b100));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b101));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b110));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
                  ##0 (! $isunknown({A1,A2,B1_N}) && {A1,A2,B1_N} == 3'b111));

  // Coverage: Y toggles
  cover property (@(posedge Y) 1'b1);
  cover property (@(negedge Y) 1'b1);

endmodule

// Bind into DUT
bind sky130_fd_sc_ms__a21boi_4 sky130_fd_sc_ms__a21boi_4_sva sva_inst (.*);
// SVA for magnitude_comparison
module magnitude_comparison_sva #(parameter WIDTH=4)
(
  input logic [WIDTH-1:0] A,
  input logic [WIDTH-1:0] B,
  input logic              eq,
  input logic              gt
);

  // Sample on any relevant change (combinational DUT)
  // Functional correctness (4-state exact match to DUT semantics)
  assert property (@(A or B or eq or gt) eq === (A == B));
  assert property (@(A or B or eq or gt) gt === (A > B));

  // Mutual exclusion when outputs are known
  assert property (@(A or B or eq or gt) (eq === 1) |-> (gt === 0));
  assert property (@(A or B or eq or gt) (gt === 1) |-> (eq === 0));

  // No X on outputs when inputs are 2-state
  assert property (@(A or B or eq or gt) !$isunknown({A,B}) |-> !$isunknown({eq,gt}));

  // Full trichotomy classification when inputs are 2-state
  assert property (@(A or B or eq or gt)
    !$isunknown({A,B}) |->
      ( (eq && (A==B)) ||
        (gt && (A>B))  ||
        (!eq && !gt && (A<B)) )
  );

  // Coverage: all relation classes and key boundaries
  cover property (@(A or B or eq or gt) (A==B) && (eq==1) && (gt==0));
  cover property (@(A or B or eq or gt) (A>B)  && (gt==1) && (eq==0));
  cover property (@(A or B or eq or gt) (A<B)  && (gt==0) && (eq==0));

  cover property (@(A or B or eq or gt) (A==0  && B==0)  && (eq==1) && (gt==0));
  cover property (@(A or B or eq or gt) (A==0  && B==15) && (gt==0) && (eq==0));
  cover property (@(A or B or eq or gt) (A==15 && B==0)  && (gt==1) && (eq==0));
  cover property (@(A or B or eq or gt) (A==15 && B==15) && (eq==1) && (gt==0));
  cover property (@(A or B or eq or gt) (A==7  && B==8)  && (gt==0) && (eq==0));
  cover property (@(A or B or eq or gt) (A==8  && B==7)  && (gt==1) && (eq==0));

endmodule

// Bind into DUT
bind magnitude_comparison magnitude_comparison_sva #(.WIDTH(4)) magnitude_comparison_sva_i (.*);
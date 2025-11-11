// SVA checker for addsub_4bit
module addsub_4bit_sva (
  input  logic [3:0] A, B,
  input  logic       M,
  input  logic [3:0] Y,
  input  logic       O
);

  // Functional correctness (5-bit accurate) with X-safety and ##0 to avoid delta races
  property p_add_correct;
    @(A or B or M or Y or O)
      (M==1'b0 && !$isunknown({A,B,M}))
      |-> ##0 {O,Y} == ({1'b0,A} + {1'b0,B});
  endproperty
  assert property (p_add_correct);

  property p_sub_correct;
    @(A or B or M or Y or O)
      (M==1'b1 && !$isunknown({A,B,M}))
      |-> ##0 {O,Y} == ({1'b0,A} - {1'b0,B});
  endproperty
  assert property (p_sub_correct);

  // Outputs must be known when inputs are known
  property p_known_out;
    @(A or B or M or Y or O)
      (!$isunknown({A,B,M})) |-> ##0 !$isunknown({O,Y});
  endproperty
  assert property (p_known_out);

  // Coverage: add w/o carry, add with carry, sub w/o borrow, sub with borrow
  cover property (@(A or B or M) (M==1'b0 && (({1'b0,A}+{1'b0,B})[4]==1'b0)));
  cover property (@(A or B or M) (M==1'b0 && (({1'b0,A}+{1'b0,B})[4]==1'b1)));
  cover property (@(A or B or M) (M==1'b1 && (A>=B)));
  cover property (@(A or B or M) (M==1'b1 && (A< B)));

endmodule

// Bind into the DUT
bind addsub_4bit addsub_4bit_sva u_addsub_4bit_sva (.*);
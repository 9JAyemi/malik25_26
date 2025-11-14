// SVA for MUX4to1
// Bind into DUT to check internal sel0/sel1 as well as Y functionality

module MUX4to1_sva (
  input logic       A, B, C, D,
  input logic [1:0] S,
  input logic       Y,
  input logic       sel0, sel1
);

  // Reference expressions
  let y_by_S   = (S===2'b00) ? A :
                 (S===2'b01) ? B :
                 (S===2'b10) ? C : D;

  let y_by_sel = (sel1 & sel0 & A) |
                 (sel1 & ~sel0 & B) |
                 (~sel1 & sel0 & C) |
                 (~sel1 & ~sel0 & D);

  // Decode checks
  assert property (sel0 === ~S[0]);
  assert property (sel1 === ~S[1]);

  // Functional correctness (known select)
  assert property ( !$isunknown(S) |-> (Y === y_by_S) );

  // Gate-level composition consistency
  assert property ( Y === y_by_sel );

  // Unique one-hot term when select is known
  assert property (
    !$isunknown(S) |-> $onehot({(~S[1] & ~S[0]),
                                (~S[1] &  S[0]),
                                ( S[1] & ~S[0]),
                                ( S[1] &  S[0])})
  );

  // Path coverage (each select value taken)
  cover property (S===2'b00 && (Y===A));
  cover property (S===2'b01 && (Y===B));
  cover property (S===2'b10 && (Y===C));
  cover property (S===2'b11 && (Y===D));

endmodule

bind MUX4to1 MUX4to1_sva MUX4to1_sva_i(
  .A(A), .B(B), .C(C), .D(D), .S(S), .Y(Y), .sel0(sel0), .sel1(sel1)
);
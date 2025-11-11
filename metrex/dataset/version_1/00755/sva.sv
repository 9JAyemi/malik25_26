// SVA for mux2to1 and mux4to1 (concise, high-quality checks + coverage)

// 2:1 MUX SVA
module mux2to1_sva (
  input logic I0, I1, S, Y
);
  // Functional correctness when inputs are known; also ensures no X on Y
  property p_m2_func_noX;
    @(I0 or I1 or S or Y)
      !$isunknown({I0,I1,S}) |-> (Y == (S ? I1 : I0) && !$isunknown(Y));
  endproperty
  assert property (p_m2_func_noX);

  // Select value coverage
  cover property (@(S) S===1'b0);
  cover property (@(S) S===1'b1);

  // Data pass-through coverage when selected data toggles
  cover property (@(I0 or S or Y) (!$isunknown(S) && S==1'b0 && $changed(I0)) ##0 (Y==I0));
  cover property (@(I1 or S or Y) (!$isunknown(S) && S==1'b1 && $changed(I1)) ##0 (Y==I1));

  // Output updates correctly on select toggle (with known inputs)
  cover property (@(S or I0 or I1) (!$isunknown({I0,I1,S}) && $changed(S)) ##0 (Y==(S?I1:I0)));
endmodule

bind mux2to1 mux2to1_sva m2_sva(.I0(I0), .I1(I1), .S(S), .Y(Y));


// 4:1 MUX SVA
module mux4to1_sva (
  input logic A, B, C, D, S0, S1, Y
);
  // Functional correctness for all known inputs/selects; also ensures no X on Y
  property p_m4_func_noX;
    @(A or B or C or D or S0 or S1 or Y)
      !$isunknown({A,B,C,D,S0,S1}) |->
        (Y == (S0 ? (S1 ? D : C) : (S1 ? B : A)) && !$isunknown(Y));
  endproperty
  assert property (p_m4_func_noX);

  // Select combination coverage
  cover property (@(S0 or S1) (S0===1'b0 && S1===1'b0));
  cover property (@(S0 or S1) (S0===1'b0 && S1===1'b1));
  cover property (@(S0 or S1) (S0===1'b1 && S1===1'b0));
  cover property (@(S0 or S1) (S0===1'b1 && S1===1'b1));

  // Data pass-through coverage when selected input toggles
  cover property (@(A or S0 or S1 or Y) (!$isunknown({S0,S1}) && S0==1'b0 && S1==1'b0 && $changed(A)) ##0 (Y==A));
  cover property (@(B or S0 or S1 or Y) (!$isunknown({S0,S1}) && S0==1'b0 && S1==1'b1 && $changed(B)) ##0 (Y==B));
  cover property (@(C or S0 or S1 or Y) (!$isunknown({S0,S1}) && S0==1'b1 && S1==1'b0 && $changed(C)) ##0 (Y==C));
  cover property (@(D or S0 or S1 or Y) (!$isunknown({S0,S1}) && S0==1'b1 && S1==1'b1 && $changed(D)) ##0 (Y==D));

  // Output updates correctly on select toggle (with known inputs)
  cover property (@(S0 or S1 or A or B or C or D)
    (!$isunknown({A,B,C,D,S0,S1}) && ($changed(S0) || $changed(S1))) ##0
      (Y == (S0 ? (S1 ? D : C) : (S1 ? B : A))));
endmodule

bind mux4to1 mux4to1_sva m4_sva(.A(A), .B(B), .C(C), .D(D), .S0(S0), .S1(S1), .Y(Y));
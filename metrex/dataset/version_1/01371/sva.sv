// SVA checkers for mux2to1 and mux4to1, with concise but high-quality functional checks and coverage.
// Bind these to the DUTs; no clock required (event-based @(*) sampling).

// ---------------- mux2to1 SVA ----------------
module mux2to1_sva (input logic A, B, S, Y);

  // Functional correctness when select is known
  assert property (@(*)
    (S inside {1'b0,1'b1}) |-> (Y === (S ? B : A))
  );

  // X-merge robustness: equal inputs force output regardless of S (even if X/Z)
  assert property (@(*) (A === B) |-> (Y === A));

  // Propagation when selected input changes
  assert property (@(*)
    (S === 1'b0 && $changed(A)) |-> ##0 ($changed(Y) && Y === A)
  );
  assert property (@(*)
    (S === 1'b1 && $changed(B)) |-> ##0 ($changed(Y) && Y === B)
  );

  // Coverage: both select values and data-path observability
  cover property (@(*) (S === 1'b0));
  cover property (@(*) (S === 1'b1));
  cover property (@(*) (S === 1'b0 && $changed(A) && $changed(Y)));
  cover property (@(*) (S === 1'b1 && $changed(B) && $changed(Y)));

endmodule

bind mux2to1 mux2to1_sva m2_sva (.A(A), .B(B), .S(S), .Y(Y));


// ---------------- mux4to1 SVA ----------------
module mux4to1_sva (input logic D0, D1, D2, D3, S0, S1, Y);

  // Full functional correctness when both selects are known
  assert property (@(*)
    ((S0 inside {0,1}) && (S1 inside {0,1})) |->
      (Y === (S0 ? (S1 ? D3 : D2) : (S1 ? D1 : D0)))
  );

  // Structural/internal stage checks (bound inside mux4to1; w1/w2/w3 are visible here)
  assert property (@(*)
    (S1 inside {0,1}) |-> (w1 === (S1 ? D1 : D0))
  );
  assert property (@(*)
    (S1 inside {0,1}) |-> (w2 === (S1 ? D3 : D2))
  );
  assert property (@(*)
    (S0 inside {0,1}) |-> (w3 === (S0 ? w2  : w1))
  );
  assert property (@(*) Y === w3);

  // X-merge robustness: equal arms collapse output even with unknown select(s)
  assert property (@(*)
    (S0 === 1'b0 && (D0 === D1)) |-> (Y === D0)
  );
  assert property (@(*)
    (S0 === 1'b1 && (D2 === D3)) |-> (Y === D2)
  );
  // If both halves collapse to the same value, output must equal that value regardless of S0/S1
  assert property (@(*)
    ((D0 === D1) && (D2 === D3) && (D0 === D2)) |-> (Y === D0)
  );

  // Propagation: when a selected data input changes, Y must change in the same delta
  assert property (@(*)
    (S0 === 1'b0 && S1 === 1'b0 && $changed(D0)) |-> ##0 ($changed(Y) && Y === D0)
  );
  assert property (@(*)
    (S0 === 1'b0 && S1 === 1'b1 && $changed(D1)) |-> ##0 ($changed(Y) && Y === D1)
  );
  assert property (@(*)
    (S0 === 1'b1 && S1 === 1'b0 && $changed(D2)) |-> ##0 ($changed(Y) && Y === D2)
  );
  assert property (@(*)
    (S0 === 1'b1 && S1 === 1'b1 && $changed(D3)) |-> ##0 ($changed(Y) && Y === D3)
  );

  // Coverage: exercise all select combinations and observe data-path toggles reaching Y
  cover property (@(*) (S0 === 1'b0 && S1 === 1'b0));
  cover property (@(*) (S0 === 1'b0 && S1 === 1'b1));
  cover property (@(*) (S0 === 1'b1 && S1 === 1'b0));
  cover property (@(*) (S0 === 1'b1 && S1 === 1'b1));

  cover property (@(*) (S0 === 1'b0 && S1 === 1'b0 && $changed(D0) && $changed(Y)));
  cover property (@(*) (S0 === 1'b0 && S1 === 1'b1 && $changed(D1) && $changed(Y)));
  cover property (@(*) (S0 === 1'b1 && S1 === 1'b0 && $changed(D2) && $changed(Y)));
  cover property (@(*) (S0 === 1'b1 && S1 === 1'b1 && $changed(D3) && $changed(Y)));

endmodule

bind mux4to1 mux4to1_sva m4_sva (.D0(D0), .D1(D1), .D2(D2), .D3(D3), .S0(S0), .S1(S1), .Y(Y));
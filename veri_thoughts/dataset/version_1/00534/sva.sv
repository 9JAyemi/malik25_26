// SVA for signal_mux
module signal_mux_sva (
  input logic A1,
  input logic A2,
  input logic A3,
  input logic B1,
  input logic X
);

  // No-X on X when inputs are known
  always_comb begin
    if (!$isunknown({A1,A2,A3,B1})) begin
      assert #0 (! $isunknown(X))
        else $error("signal_mux: X is X/Z with known inputs");
    end
  end

  // Functional equivalence (concise, partitioned)
  always_comb begin
    if (!$isunknown({A1,A2,A3,B1})) begin
      assert #0 (A1 -> (X === A2))
        else $error("signal_mux: A1=1 path violated (X != A2)");
      assert #0 (!A1 -> (X === (B1 & (A2 | A3))))
        else $error("signal_mux: A1=0 path violated (X != B1&(A2|A3))");
    end
  end

  // Full functional coverage of key cubes and X=0 case (with known inputs)
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge A3 or negedge A3 or
                    posedge B1 or negedge B1)
                  (!$isunknown({A1,A2,A3,B1}) && A1 && A2 && X));  // term: A1&A2

  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge A3 or negedge A3 or
                    posedge B1 or negedge B1)
                  (!$isunknown({A1,A2,A3,B1}) && !A1 && A3 && B1 && X)); // term: ~A1&A3&B1

  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge A3 or negedge A3 or
                    posedge B1 or negedge B1)
                  (!$isunknown({A1,A2,A3,B1}) && !A1 && !A3 && A2 && B1 && X)); // term: ~A1&~A3&A2&B1

  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge A3 or negedge A3 or
                    posedge B1 or negedge B1)
                  (!$isunknown({A1,A2,A3,B1}) && !X)); // at least one X=0 sample

endmodule

// Bind into DUT
bind signal_mux signal_mux_sva sva_inst (
  .A1(A1),
  .A2(A2),
  .A3(A3),
  .B1(B1),
  .X (X)
);
// SVA for sky130_fd_sc_ls__xor3
// Bind-in, concise, 4-state accurate, with functional checks and coverage.

module sky130_fd_sc_ls__xor3_sva
(
  input logic A, B, C, X
);

  // Functional correctness and 4-state behavior
  always_comb begin
    // Buffer transparency + 3-input XOR function (4-state equality)
    assert #0 (X === (A ^ B ^ C))
      else $error("xor3 func mismatch: X=%b A=%b B=%b C=%b", X,A,B,C);

    // Known inputs must yield known output
    if (!$isunknown({A,B,C})) begin
      assert #0 (!$isunknown(X))
        else $error("xor3 X unknown with known inputs: A=%b B=%b C=%b X=%b",A,B,C,X);
    end

    // Any unknown on inputs must propagate to X (primitive xor semantics)
    if ($isunknown({A,B,C})) begin
      assert #0 ($isunknown(X))
        else $error("xor3 X not unknown when inputs unknown: A=%b B=%b C=%b X=%b",A,B,C,X);
    end

    // Functional coverage of all input combinations and both X values
    cover ({A,B,C}==3'b000);
    cover ({A,B,C}==3'b001);
    cover ({A,B,C}==3'b010);
    cover ({A,B,C}==3'b011);
    cover ({A,B,C}==3'b100);
    cover ({A,B,C}==3'b101);
    cover ({A,B,C}==3'b110);
    cover ({A,B,C}==3'b111);
    cover (X===1'b0);
    cover (X===1'b1);
    cover ($isunknown({A,B,C}) && $isunknown(X));
  end

  // Toggle coverage for X on any input edge
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C) $rose(X));
  cover property (@(posedge A or negedge A or
                    posedge B or negedge B or
                    posedge C or negedge C) $fell(X));

endmodule

bind sky130_fd_sc_ls__xor3 sky130_fd_sc_ls__xor3_sva sva (.A(A), .B(B), .C(C), .X(X));
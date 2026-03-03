// SVA checker for Select_AB
module Select_AB_sva (
  input logic in_select,
  input logic in1,
  input logic in2,
  input logic A,
  input logic B
);

  // Combinational checks and coverage
  always_comb begin
    // 4-state functional equivalence (matches Verilog ?: with X semantics)
    assert (A === ((in_select==1'b0) ? in2 : in1))
      else $error("A mismatch: sel=%b in1=%b in2=%b A=%b", in_select,in1,in2,A);
    assert (B === ((in_select==1'b0) ? in1 : in2))
      else $error("B mismatch: sel=%b in1=%b in2=%b B=%b", in_select,in1,in2,B);

    // Permutation invariants
    assert ((A ^ B) === (in1 ^ in2))
      else $error("XOR invariant failed: A^B != in1^in2");
    assert ((A | B) === (in1 | in2))
      else $error("OR invariant failed: A|B != in1|in2");
    assert ((A & B) === (in1 & in2))
      else $error("AND invariant failed: A&B != in1&in2");

    // Knownness: if inputs known, outputs must be known
    if (!$isunknown({in_select,in1,in2})) begin
      assert (!$isunknown({A,B}))
        else $error("Outputs unknown with known inputs");
    end

    // X-select semantics: propagate or resolve X correctly
    if ($isunknown(in_select)) begin
      if (in1 === in2) begin
        assert (A === in1 && B === in1)
          else $error("X-select with equal inputs should resolve to that value");
      end else begin
        assert ($isunknown(A) && $isunknown(B))
          else $error("X-select with differing inputs should yield X outputs");
      end
    end

    // Functional coverage
    cover (in_select==1'b0 && A===in2 && B===in1);
    cover (in_select==1'b1 && A===in1 && B===in2);

    // Input space coverage (all 8 combos)
    cover ({in_select,in1,in2}==3'b000);
    cover ({in_select,in1,in2}==3'b001);
    cover ({in_select,in1,in2}==3'b010);
    cover ({in_select,in1,in2}==3'b011);
    cover ({in_select,in1,in2}==3'b100);
    cover ({in_select,in1,in2}==3'b101);
    cover ({in_select,in1,in2}==3'b110);
    cover ({in_select,in1,in2}==3'b111);

    // X-behavior coverage
    cover ($isunknown(in_select) && (in1!==in2) && $isunknown({A,B}));
    cover ($isunknown(in_select) && (in1===in2) && (A===in1) && (B===in1));
  end

endmodule

// Bind to DUT
bind Select_AB Select_AB_sva sva_i (
  .in_select(in_select),
  .in1(in1),
  .in2(in2),
  .A(A),
  .B(B)
);
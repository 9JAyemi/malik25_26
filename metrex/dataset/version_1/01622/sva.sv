// SVA for top_module, magnitude_comparator, and barrel_shifter
// Bind-friendly, combinational (no clock required), concise, with key coverage.

module mag_comp_sva (input logic [15:0] A, B, input logic A_greater_B);
  // Correctness and X-prop
  always_comb begin
    if (!$isunknown({A,B})) begin
      assert (((A > B) ? 1'b1 : 1'b0) == A_greater_B)
        else $error("mag_comp: A_greater_B mismatch A(%0h) > B(%0h)", A, B);
    end
    assert ($isunknown({A,B}) || !$isunknown(A_greater_B))
      else $error("mag_comp: X on output with clean inputs");
  end

  // Coverage: all compare outcomes
  always_comb begin
    cover (! $isunknown({A,B}) && (A >  B) &&  A_greater_B);
    cover (! $isunknown({A,B}) && (A == B) && !A_greater_B);
    cover (! $isunknown({A,B}) && (A <  B) && !A_greater_B);
  end
endmodule

module barrel_shifter_sva (
  input logic [15:0] A, B,
  input logic [3:0]  shift_amount,
  input logic        A_greater_B,
  input logic [15:0] result
);
  // Functional check exactly matches DUT's priority
  always_comb begin
    if (!$isunknown({A,B,shift_amount,A_greater_B})) begin
      assert ( A_greater_B
               ? (result == (A << shift_amount))
               : ( (A < B)
                   ? (result == (B >> shift_amount))
                   : (result == A) ) )
        else $error("barrel_shifter: result mismatch A=%0h B=%0h sa=%0d A>B=%0b res=%0h",
                    A,B,shift_amount,A_greater_B,result);
    end
    assert ($isunknown({A,B,shift_amount,A_greater_B}) || !$isunknown(result))
      else $error("barrel_shifter: X on result with clean inputs");
  end

  // Coverage: left/right/no-shift paths and edge shift amounts
  always_comb begin
    // Left shift path
    cover (! $isunknown({A,shift_amount,A_greater_B}) && A_greater_B && shift_amount==0  && (result==(A<<0)));
    cover (! $isunknown({A,shift_amount,A_greater_B}) && A_greater_B && shift_amount==15 && (result==(A<<15)));
    // Right shift path
    cover (! $isunknown({B,shift_amount,A_greater_B,A,B}) && !A_greater_B && (A<B) && shift_amount==0  && (result==(B>>0)));
    cover (! $isunknown({B,shift_amount,A_greater_B,A,B}) && !A_greater_B && (A<B) && shift_amount==15 && (result==(B>>15)));
    // Equal case path
    cover (! $isunknown({A,B,A_greater_B}) && !A_greater_B && (A==B) && (result==A));
  end
endmodule

module top_compose_sva (
  input logic [15:0] A, B,
  input logic [3:0]  shift_amount,
  input logic [15:0] result
);
  // End-to-end check of composed behavior (independent of internal A_greater_B)
  always_comb begin
    if (!$isunknown({A,B,shift_amount})) begin
      assert ( (A > B)  ? (result == (A << shift_amount)) :
               (A < B)  ? (result == (B >> shift_amount)) :
                          (result == A) )
        else $error("top: end-to-end result mismatch A=%0h B=%0h sa=%0d res=%0h",
                    A,B,shift_amount,result);
    end
  end

  // Coverage: all three top-level behaviors observed
  always_comb begin
    cover (! $isunknown({A,B,shift_amount}) && (A > B) && (result==(A<<shift_amount)));
    cover (! $isunknown({A,B,shift_amount}) && (A < B) && (result==(B>>shift_amount)));
    cover (! $isunknown({A,B})             && (A == B) && (result==A));
  end
endmodule

// Bind assertions into DUT
bind magnitude_comparator mag_comp_sva mag_comp_sva_i (.*);
bind barrel_shifter      barrel_shifter_sva barrel_shifter_sva_i (.*);
bind top_module          top_compose_sva top_compose_sva_i (.*);
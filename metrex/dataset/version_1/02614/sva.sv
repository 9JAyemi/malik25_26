// SVA for add_sub_4bit
// Bind these modules to the DUT. Focused, concise checks + key coverage.

// Functional correctness and scenario coverage (uses only DUT ports)
module add_sub_4bit_sva (
  input  signed [3:0] A,
  input  signed [3:0] B,
  input               mode,
  input  signed [3:0] result
);

  function automatic [3:0] wrap_add4 (input signed [3:0] x, y);
    logic signed [4:0] s;
    s = $signed({x[3],x}) + $signed({y[3],y});
    return s[3:0];
  endfunction

  function automatic [3:0] wrap_sub4 (input signed [3:0] x, y);
    logic signed [4:0] s;
    s = $signed({x[3],x}) - $signed({y[3],y});
    return s[3:0];
  endfunction

  // Immediate SVA: combinational correctness, X-prop
  always_comb begin
    if (!$isunknown({A,B,mode})) begin
      assert (result === (mode ? wrap_add4(A,B) : wrap_sub4(A,B)))
        else $error("add_sub_4bit mismatch: A=%0d B=%0d mode=%0b got=%0d exp=%0d",
                    $signed(A), $signed(B), mode, $signed(result),
                    $signed(mode ? wrap_add4(A,B) : wrap_sub4(A,B)));

      // Equivalence: A - B == A + (~B + 1) (mod 4 bits)
      assert (wrap_sub4(A,B) === wrap_add4(A, $signed((~B)+4'b0001)))
        else $error("Two's complement equivalence failed: A=%0d B=%0d", $signed(A), $signed(B));

      // Result should not be X/Z for clean inputs
      assert (!$isunknown(result))
        else $error("Result X/Z with clean inputs: A=%0d B=%0d mode=%0b", $signed(A), $signed(B), mode);
    end

    // Basic functional coverage
    cover (!$isunknown({A,B,mode}) &&  mode && (result === wrap_add4(A,B))); // add path hit
    cover (!$isunknown({A,B,mode}) && !mode && (result === wrap_sub4(A,B))); // sub path hit

    // Signed overflow coverage (classic criteria)
    cover (!$isunknown({A,B,mode}) &&  mode && (A[3]==B[3]) && (result[3]!=A[3])); // add overflow
    cover (!$isunknown({A,B,mode}) && !mode && (A[3]!=B[3]) && (result[3]!=A[3])); // sub overflow

    // Boundary/interesting cases
    cover (!$isunknown({A,B,mode}) && (result ==  4'sd7));
    cover (!$isunknown({A,B,mode}) && (result == -4'sd8));
    cover (!$isunknown({A,B,mode}) && (B==4'sd0) && (result==A));
    cover (!$isunknown({A,B,mode}) && (A==4'sd0) &&  mode && (result==B));
    cover (!$isunknown({A,B,mode}) && (A==4'sd0) && !mode && (result==$signed(-B)));
    cover (!$isunknown({A,B,mode}) && (B==-4'sd8)); // special two's-comp self case
  end

endmodule

bind add_sub_4bit add_sub_4bit_sva u_add_sub_4bit_sva (.A(A), .B(B), .mode(mode), .result(result));


// Internal signal check (verifies two's complement wire behavior)
module add_sub_4bit_int_sva;
  // twos_comp_B should always be ~B + 1; cover special -8 case
  always_comb begin
    if (!$isunknown(B)) begin
      assert (twos_comp_B === ((~B)+4'b0001))
        else $error("twos_comp_B incorrect: B=%0d twos_comp_B=%0d", $signed(B), $signed(twos_comp_B));
      cover (B == -4'sd8 && twos_comp_B == -4'sd8);
    end
  end
endmodule

bind add_sub_4bit add_sub_4bit_int_sva u_add_sub_4bit_int_sva();
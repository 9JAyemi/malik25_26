// SVA checker for adder_subtractor (combinational, clockless using #0 sampling)
module adder_subtractor_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       subtract,
  input logic [3:0] result
);
  // Combinational correctness and X/Z checks (sample after NBA using #0)
  always @* begin
    assert (!$isunknown({A,B,subtract}))
      else $error("adder_subtractor: X/Z on inputs A=%b B=%b subtract=%b", A,B,subtract);

    assert (#0 !$isunknown(result))
      else $error("adder_subtractor: X/Z on result=%b", result);

    assert (#0 (subtract ? (result == ((A - B) & 4'hF))
                          : (result == ((A + B) & 4'hF))))
      else $error("adder_subtractor: mismatch A=%0d B=%0d sub=%0b result=%0d exp=%0d",
                  A, B, subtract, result,
                  subtract ? ((A - B) & 4'hF) : ((A + B) & 4'hF));
  end

  // Functional coverage (sample after NBA using #0)
  always @* begin
    cover (#0 (subtract==1'b0));                  // add mode seen
    cover (#0 (subtract==1'b1));                  // sub mode seen
    cover (#0 ({1'b0,A}+{1'b0,B})[4]);            // add overflow (carry out)
    cover (#0 (subtract && (A < B)));             // sub underflow (borrow)
    cover (#0 (subtract==1'b0 && result==4'h0));  // add wraps to 0
    cover (#0 (subtract==1'b1 && result==4'h0));  // sub equals 0 (A==B)
    cover (#0 (result==4'hF));                    // max result reached
    cover (#0 (A==4'h0)); cover (#0 (B==4'h0));   // operand zeros
    cover (#0 (A==4'hF)); cover (#0 (B==4'hF));   // operand max
    cover (#0 $changed(subtract));                // mode toggle exercised
  end
endmodule

// Bind into DUT
bind adder_subtractor adder_subtractor_sva u_adder_subtractor_sva (.*);
// SVA checker for add_sub_4bit
module add_sub_4bit_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       mode,
  input logic [3:0] sum,
  input logic       carry_borrow
);
  always_comb begin
    automatic logic [4:0] gold;
    gold = mode ? ({1'b0,A} - {1'b0,B}) : ({1'b0,A} + {1'b0,B});

    // Inputs must be known
    assert (!$isunknown({A,B,mode}))
      else $error("add_sub_4bit: X/Z on inputs A=%0h B=%0h mode=%b", A,B,mode);

    if (!$isunknown({A,B,mode})) begin
      // Outputs must be known when inputs are known
      assert (!$isunknown({sum,carry_borrow}))
        else $error("add_sub_4bit: X/Z on outputs with known inputs");

      // Functional correctness
      assert (sum == gold[3:0])
        else $error("add_sub_4bit: sum mismatch mode=%b A=%0h B=%0h got=%0h exp=%0h",
                    mode,A,B,sum,gold[3:0]);

      assert (carry_borrow == gold[4])
        else $error("add_sub_4bit: carry/borrow mismatch mode=%b A=%0h B=%0h got=%0b exp=%0b",
                    mode,A,B,carry_borrow,gold[4]);
    end

    // Minimal functional coverage
    cover (!$isunknown({A,B,mode}) && (mode==1'b0) && (gold[4]==1'b0)); // add, no carry
    cover (!$isunknown({A,B,mode}) && (mode==1'b0) && (gold[4]==1'b1)); // add, with carry
    cover (!$isunknown({A,B,mode}) && (mode==1'b1) && (gold[4]==1'b0)); // sub, no borrow
    cover (!$isunknown({A,B,mode}) && (mode==1'b1) && (gold[4]==1'b1)); // sub, with borrow
  end
endmodule

// Bind into the DUT
bind add_sub_4bit add_sub_4bit_sva u_add_sub_4bit_sva (.*);
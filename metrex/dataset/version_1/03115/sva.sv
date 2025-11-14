// SVA for arithmetic_unit (concise, covers functionality and priority selection)
`ifndef ARITHMETIC_UNIT_SVA
`define ARITHMETIC_UNIT_SVA

module arithmetic_unit_sva (
  input  logic [15:0] a,
  input  logic [15:0] b,
  input  logic [1:0]  op,
  input  logic [31:0] result
);

  // Recompute expected behavior (16-bit wrap, zero-extended to 32)
  logic [15:0] exp_sum, exp_diff, exp_and, exp_sel16;
  logic [31:0] exp_result;
  logic [16:0] sum17;

  always_comb begin
    exp_sum    = a + b;
    exp_diff   = a - b;
    exp_and    = a & b;
    exp_sel16  = (op==2'b10) ? exp_and :
                 (op==2'b01) ? exp_diff :
                                exp_sum;   // includes op==00 and op==11
    exp_result = {16'd0, exp_sel16};
    sum17      = {1'b0,a} + {1'b0,b};      // for overflow coverage
  end

  // Assertions (guarded against X/Z on inputs)
  always_comb begin
    if (!$isunknown({a,b,op})) begin
      assert (result == exp_result)
        else $error("arithmetic_unit: result mismatch. op=%b a=%h b=%h got=%h exp=%h",
                    op,a,b,result,exp_result);

      assert (result[31:16] == 16'd0)
        else $error("arithmetic_unit: upper 16 bits must be zero. got=%h", result[31:16]);

      assert (!$isunknown(result))
        else $error("arithmetic_unit: result contains X/Z with known inputs. op=%b a=%h b=%h", op,a,b);

      // Explicit priority mapping checks
      if (op==2'b10) assert (result[15:0] == exp_and)
        else $error("arithmetic_unit: AND selection wrong.");
      else if (op==2'b01) assert (result[15:0] == exp_diff)
        else $error("arithmetic_unit: SUB selection wrong.");
      else assert (result[15:0] == exp_sum)
        else $error("arithmetic_unit: ADD selection wrong (op==00 or 11).");
    end
  end

  // Functional coverage (immediate cover statements)
  always_comb begin
    // Operation encoding exercised (including priority fallback on 11 -> ADD)
    cover (op==2'b00);
    cover (op==2'b01);
    cover (op==2'b10);
    cover (op==2'b11 && result[15:0]==exp_sum);

    // Interesting data scenarios per operation
    cover (op==2'b10 && (a&b)==16'h0000);  // AND -> zero
    cover (op==2'b10 && (a&b)!=16'h0000);  // AND -> non-zero
    cover (op==2'b01 && a<b);              // SUB borrow/wrap
    cover (op==2'b01 && a>=b);             // SUB no borrow
    cover ((op!=2'b10 && op!=2'b01) && sum17[16]); // ADD overflow on ADD path

    // Corners
    cover (a==16'h0000 && b==16'h0000);
    cover (a==16'hFFFF || b==16'hFFFF);
    cover (a==b);
  end

endmodule

// Bind to DUT (no DUT changes required)
bind arithmetic_unit arithmetic_unit_sva au_sva (.*);

`endif
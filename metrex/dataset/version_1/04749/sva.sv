// SVA for adder, max_finder, and top_module
// Bind checkers for concise, high-quality functional checking and coverage

// ---------- adder checks ----------
module adder_sva_bind (
  input [3:0] a, b,
  input       cin,
  input [3:0] sum,
  input       cout
);
  // Combinational correctness and X checks
  always_comb begin
    assert ({cout,sum} == a + b + cin)
      else $error("adder mismatch: a=%0d b=%0d cin=%0b -> {cout,sum}=%0b_%0h exp=%0d",
                  a,b,cin,cout,sum,a+b+cin);
    assert (!$isunknown({a,b,cin,sum,cout}))
      else $error("adder X/Z detected");
  end
endmodule

bind adder adder_sva_bind (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));

// ---------- max_finder checks ----------
module max_finder_sva_bind (
  input [3:0] a, b,
  input [3:0] max_val
);
  always_comb begin
    assert (max_val == ((a > b) ? a : b))
      else $error("max_finder mismatch: a=%0h b=%0h max=%0h", a,b,max_val);
    if (a == b) assert (max_val == b)
      else $error("max_finder tie preference violated (must choose b)");
    assert (!$isunknown({a,b,max_val}))
      else $error("max_finder X/Z detected");
  end
endmodule

bind max_finder max_finder_sva_bind (.a(a), .b(b), .max_val(max_val));

// ---------- top_module checks and coverage ----------
module top_module_sva_bind (
  input        clk, reset,
  input  [3:0] a, b,
  input        cin1, cin2,
  input  [3:0] sum1, sum2,
  input        cout1, cout2,
  input  [3:0] max_sum,
  // internal regs
  input  [3:0] sum1_reg, sum2_reg,
  input        cout1_reg, cout2_reg
);
  default clocking cb @(posedge clk); endclocking

  // No X on primary outputs
  assert property (!$isunknown({sum1,sum2,cout1,cout2,max_sum}))
    else $error("top outputs X/Z detected");

  // max_finder behavior at the top level
  assert property (max_sum == ((sum1 > sum2) ? sum1 : sum2))
    else $error("top max_sum mismatch");
  // Tie preference: choose sum2 when equal
  assert property ((sum1 == sum2) |-> (max_sum == sum2))
    else $error("top tie preference violated");

  // If cin1 == cin2, both adders must match
  assert property ((cin1 == cin2) |-> (sum1 == sum2 && cout1 == cout2))
    else $error("adders disagree when cin1==cin2");

  // Register reset behavior
  assert property (reset |-> (sum1_reg==4'h0 && sum2_reg==4'h0 && !cout1_reg && !cout2_reg))
    else $error("regs not cleared on reset");

  // Registers sample adder outputs cycle-to-cycle when not in reset
  assert property (disable iff (reset)
                   (sum1_reg == $past(sum1) &&
                    sum2_reg == $past(sum2) &&
                    cout1_reg == $past(cout1) &&
                    cout2_reg == $past(cout2)))
    else $error("regs did not sample previous-cycle adder outputs");

  // Basic coverage
  cover property ($fell(reset));                              // reset deassertion observed
  cover property (cout1);                                     // carry from adder1
  cover property (cout2);                                     // carry from adder2
  cover property (sum1 == sum2);                              // equal sums
  cover property (sum1 >  sum2 && max_sum == sum1);           // max from sum1
  cover property (sum1 <  sum2 && max_sum == sum2);           // max from sum2
  cover property (sum1 == sum2 && max_sum == sum2);           // tie preference exercised
  cover property (cin1==0 && cin2==1);                        // differing carry-in case
  cover property (a==4'hF && b==4'hF && cin1);                // overflow corner
endmodule

bind top_module top_module_sva_bind (
  .clk(clk), .reset(reset),
  .a(a), .b(b), .cin1(cin1), .cin2(cin2),
  .sum1(sum1), .sum2(sum2), .cout1(cout1), .cout2(cout2),
  .max_sum(max_sum),
  .sum1_reg(sum1_reg), .sum2_reg(sum2_reg),
  .cout1_reg(cout1_reg), .cout2_reg(cout2_reg)
);
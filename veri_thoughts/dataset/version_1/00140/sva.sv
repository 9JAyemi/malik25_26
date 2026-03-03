// SVA checker for addition_4bit. Bind this to the DUT.
module addition_4bit_sva #(parameter bit USE_CLOCKED = 0) (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [3:0] sum,
  input  logic       clk = 1'b0  // optional sample clock if USE_CLOCKED=1
);

  // Immediate (combinational) assertions and coverage
  always_comb begin
    if (!$isunknown({a,b})) begin
      // Functional correctness: modulo-16 sum
      assert (sum == ((a + b) & 4'hF))
        else $error("addition_4bit: wrong sum a=%0h b=%0h sum=%0h exp=%0h",
                    a, b, sum, ((a + b) & 4'hF));
      // No X on sum when inputs are known
      assert (!$isunknown(sum))
        else $error("addition_4bit: X/Z on sum with known inputs a=%0h b=%0h", a, b);
    end

    // Concise functional coverage
    cover ((a + b) < 16 && sum == (a + b));               // non-wrap path
    cover ((a + b) >= 16 && sum == ((a + b) - 16));       // wrap path
    for (int i = 0; i < 16; i++) cover (sum == i);        // all 16 results
    // Key boundary/wrap examples
    cover (a == 4'h0 && b == 4'h0 && sum == 4'h0);
    cover (a == 4'h8 && b == 4'h8 && sum == 4'h0);        // exact 16 wrap
    cover (a == 4'hF && b == 4'h1 && sum == 4'h0);        // minimal wrap
    cover (a == 4'hF && b == 4'hF && sum == 4'hE);        // max inputs
  end

  // Optional clocked concurrent SVA (useful for formal or sampled checks)
  if (USE_CLOCKED) begin : g_clk
    default clocking cb @(posedge clk); endclocking

    // Correctness when inputs are known
    property p_modsum;
      !$isunknown({a,b}) |-> (sum == ((a + b) & 4'hF));
    endproperty
    assert property (p_modsum);

    // Stability: if inputs don't change, sum doesn't change
    property p_stable;
      $stable(a) && $stable(b) |-> $stable(sum);
    endproperty
    assert property (p_stable);

    // Minimal concurrent coverage
    cover property ((a == 4'h8 && b == 4'h8) && sum == 4'h0);
    cover property ((a + b) >= 16 && sum == ((a + b) - 16));
  end

endmodule

bind addition_4bit addition_4bit_sva u_addition_4bit_sva(.a(a), .b(b), .sum(sum));
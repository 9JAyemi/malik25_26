// SVA checker for add8bit
module add8bit_sva (input [7:0] in1, input [7:0] in2, input [7:0] sum);

  // Core functional check (with X-gating) and sanity
  always_comb begin
    if (!$isunknown({in1,in2})) begin
      // 9-bit add to avoid width/signedness pitfalls; check truncated result
      assert ({1'b0,sum} == ({1'b0,in1} + {1'b0,in2}))
        else $error("add8bit: sum mismatch (in1=%0h in2=%0h sum=%0h)", in1, in2, sum);
      assert (!$isunknown(sum))
        else $error("add8bit: X/Z on sum with known inputs (in1=%0h in2=%0h)", in1, in2);
    end
  end

  // Focused functional coverage
  always_comb begin
    cover (in1==8'h00 && sum==in2);                       // identity: +0
    cover (in2==8'h00 && sum==in1);                       // identity: 0+
    cover (({1'b0,in1}+{1'b0,in2})[8]);                   // overflow/wrap occurred
    cover (in1==8'hFF && in2==8'h01 && sum==8'h00);       // specific wrap-around
    cover (sum==8'h00);                                   // zero result
    cover (sum==8'hFF);                                   // max result
  end

endmodule

// Bind the checker to the DUT
bind add8bit add8bit_sva u_add8bit_sva(.in1(in1), .in2(in2), .sum(sum));
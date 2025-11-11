// SVA checker for adder; bind to DUT
module adder_sva(input logic [3:0] a, input logic [3:0] b, input logic [4:0] sum);

  function automatic [4:0] mod16_sum(input logic [3:0] aa, input logic [3:0] bb);
    mod16_sum = {1'b0, (aa + bb)[3:0]};
  endfunction

  // Sample on any combinational change
  event comb_ev; always @* -> comb_ev;

  // No X/Z on interface
  assert property (@(comb_ev) !$isunknown({a,b,sum}));

  // Functional equivalence: modulo-16, zero-extended
  assert property (@(comb_ev) disable iff ($isunknown({a,b}))
                   sum == mod16_sum(a,b));

  // Redundant but explicit nibble/overflow checks
  assert property (@(comb_ev) sum[4] == 1'b0);
  assert property (@(comb_ev) disable iff ($isunknown({a,b}))
                   sum[3:0] == (a + b)[3:0]);
  assert property (@(comb_ev) disable iff ($isunknown({a,b}))
                   (a + b <= 5'd15) |-> sum == (a + b));
  assert property (@(comb_ev) disable iff ($isunknown({a,b}))
                   (a + b >  5'd15) |-> sum == mod16_sum(a,b));

  // Coverage: hit non-overflow, overflow, and key boundaries
  cover property (@(comb_ev) (a + b <= 5'd15) && (sum == (a + b)));
  cover property (@(comb_ev) (a + b >  5'd15) && (sum == mod16_sum(a,b)));
  cover property (@(comb_ev) a == 4'd0  && b == 4'd0  && sum == 5'd0);
  cover property (@(comb_ev) a == 4'd7  && b == 4'd8  && sum == 5'd15); // max no overflow
  cover property (@(comb_ev) a == 4'd15 && b == 4'd1  && sum == 5'd0);  // wrap to 0
  cover property (@(comb_ev) a == 4'd15 && b == 4'd15 && sum == 5'd14); // max input sum
endmodule

bind adder adder_sva u_adder_sva (.a(a), .b(b), .sum(sum));
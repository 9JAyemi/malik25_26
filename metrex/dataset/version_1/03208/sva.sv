// SVA for calc: concise, high-quality checks and coverage
module calc_sva #(parameter W=4)(
  input logic [W-1:0] num1,
  input logic [W-1:0] num2,
  input logic         op,
  input logic [W-1:0] result
);

  // Check everything on any combinational activity; defer comparisons to end of timestep
  always @* begin
    // No X/Z on inputs (prevents X-optimistic if/else behavior)
    assert (!$isunknown({op,num1,num2}))
      else $error("calc: X/Z on inputs: op=%b num1=%h num2=%h", op, num1, num2);

    // Expected value and overflow/borrow helpers
    automatic logic [W-1:0] exp   = op ? (num1 - num2) : (num1 + num2);
    automatic logic [W:0]   sum5  = {1'b0,num1} + {1'b0,num2};
    automatic logic [W:0]   diff5 = {1'b0,num1} - {1'b0,num2};

    // Functional equivalence (deferred immediate assert to avoid NBA race)
    assert final (result === exp)
      else $error("calc mismatch: op=%0b num1=%0h num2=%0h exp=%0h got=%0h",
                  op, num1, num2, exp, result);

    // Minimal but meaningful functional coverage
    cover (op==0);                // addition exercised
    cover (op==1);                // subtraction exercised
    cover ((op==0) && sum5[W]);   // addition overflow (carry out)
    cover ((op==1) && diff5[W]);  // subtraction borrow (underflow)
    cover (result==0);            // zero result case
  end

endmodule

// Bind into DUT
bind calc calc_sva #(.W(4)) u_calc_sva (.*);
// SVA checker for boothMultiplier
// Quality-focused, concise assertions + coverage.
// Bind this module to the DUT.

module boothMultiplier_sva
(
  input  logic        clock,
  input  logic        reset,
  input  logic [3:0]  multiplicand,
  input  logic [3:0]  multiplier,
  input  logic [7:0]  product,
  input  logic [3:0]  A, Q, M,
  input  logic        Q_1,
  input  logic [3:0]  count,
  input  logic [3:0]  sum, difference
);

  // Helpers
  function automatic signed [7:0] sext4(input logic [3:0] x);
    sext4 = $signed({{4{x[3]}}, x});
  endfunction

  // Reset behavior
  assert property (@(posedge clock)
    reset |-> (A==4'b0 && Q_1==1'b0 && count==4'b0 && M==multiplicand && Q==multiplier)
  );

  // M is latched on reset, then stable
  assert property (@(posedge clock) disable iff (reset) $stable(M));

  // Count increments every non-reset cycle
  assert property (@(posedge clock) disable iff (reset)
    count == $past(count) + 1
  );

  // Combinational ALU correctness
  assert property (@(posedge clock) sum == (A + M));
  assert property (@(posedge clock) difference == (A + (~M) + 1'b1)); // A - M (mod 16)

  // Booth step correctness (updates use previous-cycle selector and pre-ALU results)
  assert property (@(posedge clock) disable iff (reset)
    ($past({Q[0],Q_1})==2'b01) |-> {A,Q,Q_1} == { $past(sum)[3], $past(sum), $past(Q) }
  );
  assert property (@(posedge clock) disable iff (reset)
    ($past({Q[0],Q_1})==2'b10) |-> {A,Q,Q_1} == { $past(difference)[3], $past(difference), $past(Q) }
  );
  assert property (@(posedge clock) disable iff (reset)
    ($past({Q[0],Q_1}) inside {2'b00,2'b11}) |-> {A,Q,Q_1} == { $past(A)[3], $past(A), $past(Q) }
  );

  // Always shift out Q[0] into Q_1
  assert property (@(posedge clock) disable iff (reset)
    Q_1 == $past(Q[0])
  );

  // Product update timing and value
  // Product updates in the cycle where previous count==4 and equals the pre-update {A,Q}
  assert property (@(posedge clock) disable iff (reset)
    ($past(count)==4) |-> (product == $past({A,Q}))
  );
  // Product must only change when previous count==4
  assert property (@(posedge clock) disable iff (reset)
    $changed(product) |-> ($past(count)==4)
  );

  // End-to-end correctness (first post-reset operation completes in 4 steps)
  // On the first non-reset cycle, in 4 cycles product must equal signed 4x4 result
  assert property (@(posedge clock)
    ($past(reset) && !reset) |-> ##4
      (product == sext4($past(multiplicand)) * sext4($past(multiplier)))
  );

  // Coverage
  cover property (@(posedge clock) $past(reset) && !reset);                      // start
  cover property (@(posedge clock) disable iff (reset) ($past({Q[0],Q_1})==2'b01));
  cover property (@(posedge clock) disable iff (reset) ($past({Q[0],Q_1})==2'b10));
  cover property (@(posedge clock) disable iff (reset) ($past({Q[0],Q_1}) inside {2'b00,2'b11}));
  cover property (@(posedge clock)
    ($past(reset) && !reset) ##4 (product == sext4($past(multiplicand)) * sext4($past(multiplier)))
  );
  // Signed operand scenario coverage
  cover property (@(posedge clock)
    ($past(reset) && !reset && $past(multiplicand[3]) && $past(multiplier[3])) ##4 !product[7]
  );
  cover property (@(posedge clock)
    ($past(reset) && !reset && ($past(multiplicand[3]) ^ $past(multiplier[3]))) ##4 product[7]
  );

endmodule

// Bind into DUT
bind boothMultiplier boothMultiplier_sva sva_i
(
  .clock(clock),
  .reset(reset),
  .multiplicand(multiplicand),
  .multiplier(multiplier),
  .product(product),
  .A(A), .Q(Q), .M(M), .Q_1(Q_1), .count(count),
  .sum(sum), .difference(difference)
);
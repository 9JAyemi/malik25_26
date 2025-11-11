// SVA for shift_register_with_difference

module shift_register_with_difference_sva(
  input logic        clk,
  input logic        data,
  input logic [3:0]  q,
  input logic [3:0]  difference
);
  default clocking cb @(posedge clk); endclocking

  // Track $past validity
  logic past1, past2;
  initial begin past1 = 1'b0; past2 = 1'b0; end
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // 2-cycle shift behavior: q(n) == { q(n-2)[2:0], data(n-2) }
  assert property (past2 |-> q == { $past(q,2)[2:0], $past(data,2) })
    else $error("q does not match 2-cycle shift of {q[2:0], data}");

  // difference(n) == zero-extended(q(n-1)[1]) - zero-extended(q(n-1)[0])
  assert property (past1 |-> difference == ({3'b000,$past(q[1])} - {3'b000,$past(q[0])}))
    else $error("difference mismatch vs previous q[1]-q[0]");

  // difference limited to {0,1,15} whenever prior q[1:0] are known
  assert property (past1 && !$isunknown($past(q[1:0])) |-> difference inside {4'h0,4'h1,4'hF})
    else $error("difference out of expected set");

  // Knownness: if prior contributors are known, q must be known
  assert property (past2 && !$isunknown($past(q,2)[2:0]) && !$isunknown($past(data,2)) |-> !$isunknown(q));

  // Coverage
  cover property (past2 && q == { $past(q,2)[2:0], $past(data,2) });
  cover property (past1 && $past(q[1:0]) == 2'b10 && difference == 4'h1);
  cover property (past1 && $past(q[1:0]) == 2'b01 && difference == 4'hF);
  cover property (past1 && $past(q[1:0]) inside {2'b00,2'b11} && difference == 4'h0);
  cover property (past2 && $past(data,2) == 1 && q[0] == 1);
  cover property (past2 && $past(data,2) == 0 && q[0] == 0);
endmodule

bind shift_register_with_difference shift_register_with_difference_sva sva_shift_diff (
  .clk(clk),
  .data(data),
  .q(q),
  .difference(difference)
);
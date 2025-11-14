// SVA for num_operation
// Binds to DUT, checks 1-cycle latency and 4-bit wrap behavior, with key coverage.

module num_operation_sva
  (input logic clk,
   input logic [3:0] num_a, num_b,
   input logic       ctrl,
   input logic [3:0] out);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Helpers (4-bit wrap)
  function automatic logic [3:0] add4(input logic [3:0] a,b);
    add4 = (a + b) & 4'hF;
  endfunction
  function automatic logic [3:0] sub4(input logic [3:0] a,b);
    sub4 = (a - b) & 4'hF;
  endfunction

  // Core functional checks (1-cycle latency)
  property p_add;
    disable iff (!past_valid)
      !$past(ctrl) |-> (out == add4($past(num_a), $past(num_b)));
  endproperty
  assert property (p_add);

  property p_sub;
    disable iff (!past_valid)
      $past(ctrl) |-> (out == sub4($past(num_a), $past(num_b)));
  endproperty
  assert property (p_sub);

  // Known-ness: if inputs/ctrl known, output must be known next cycle
  property p_known_propagation;
    disable iff (!past_valid)
      !$isunknown({$past(num_a),$past(num_b),$past(ctrl)}) |-> !$isunknown(out);
  endproperty
  assert property (p_known_propagation);

  // Basic opcode coverage
  cover property (past_valid && !$past(ctrl));  // addition seen
  cover property (past_valid &&  $past(ctrl));  // subtraction seen

  // Corner coverage
  // Add overflow (carry out)
  cover property (past_valid && !$past(ctrl) &&
                  (({1'b0,$past(num_a)} + {1'b0,$past(num_b)})[4]));
  // Sub underflow (borrow / negative)
  cover property (past_valid &&  $past(ctrl) &&
                  (({1'b0,$past(num_a)} - {1'b0,$past(num_b)})[4]));
  // Sub result zero (a == b)
  cover property (past_valid &&  $past(ctrl) && ($past(num_a) == $past(num_b)));
  // Identity ops
  cover property (past_valid && !$past(ctrl) && ($past(num_b) == 4'd0));
  cover property (past_valid &&  $past(ctrl) && ($past(num_b) == 4'd0));
endmodule

// Bind into DUT
bind num_operation num_operation_sva u_num_operation_sva (
  .clk(clk),
  .num_a(num_a),
  .num_b(num_b),
  .ctrl(ctrl),
  .out(out)
);
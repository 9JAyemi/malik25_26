// SVA checker for module adder. Bind this into the DUT.
// Focus: pass-through correctness when add=1, registered hold when add=0,
// register update semantics, and key functional coverage.

module adder_sva #(parameter W=32)
(
  input logic              clk,
  input logic              add,
  input logic [W-1:0]      A,
  input logic [W-1:0]      B,
  input logic [W-1:0]      sum,
  // Internal register from DUT (connected via bind to adder.sum_reg)
  input logic [W-1:0]      sum_reg
);

  default clocking cb @(posedge clk); endclocking

  // Track last computed add result and whether we have a valid latched value
  logic [W-1:0] last_add_result;
  logic         seen;

  always_ff @(posedge clk) begin
    if (!$isunknown({add,A,B}) && add) begin
      last_add_result <= A + B;
      seen            <= 1'b1;
    end
  end

  // Output equals mux of combinational add vs registered value
  // Disable before any add has occurred and add is 0, or if inputs unknown.
  assert property (disable iff ((!seen && !add) || $isunknown({add,A,B})))
    sum == (add ? (A + B) : sum_reg);

  // Pass-through correctness when add=1
  assert property (disable iff ($isunknown({add,A,B})))
    add |-> (sum == (A + B));

  // On add falling edge, output takes the previously latched result
  assert property (disable iff ($isunknown({$past(add),$past(A),$past(B)})))
    $fell(add) |-> (sum == $past(A + B));

  // When add stays low, output holds stable (after at least one valid latch)
  assert property (disable iff (!seen || $isunknown({add,$past(add)})))
    (!add && $past(!add)) |-> (sum == $past(sum));

  // Internal register update semantics
  // Update on cycles with add=1
  assert property (disable iff ($isunknown({$past(add),$past(A),$past(B)})))
    $past(add) |-> (sum_reg == $past(A + B));

  // Hold when add=0
  assert property (disable iff ($isunknown($past(add))))
    !$past(add) |-> (sum_reg == $past(sum_reg));

  // Basic X-propagation sanity: when inputs and add are known, sum is known
  assert property (disable iff ($isunknown({add,A,B})))
    add |-> !$isunknown(sum);

  // Coverage
  cover property (add);                               // exercise pass-through
  cover property ($fell(add));                        // exercise latch handoff
  cover property (!add[*3] ##1 add);                  // hold stretch then add
  cover property (add [*3]);                          // consecutive adds
  cover property (add && ((A + B) < A));              // wrap/overflow scenario

endmodule

// Bind into the DUT (connects internal sum_reg)
bind adder adder_sva #(.W(32)) i_adder_sva (
  .clk     (clk),
  .add     (add),
  .A       (A),
  .B       (B),
  .sum     (sum),
  .sum_reg (sum_reg)
);
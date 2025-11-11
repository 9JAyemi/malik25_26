// SVA checker for adder. Bind this to the DUT.
module adder_sva #(parameter WIDTH=8) (
  input  logic                  clk, rst, load,
  input  logic [WIDTH-1:0]      A, B,
  input  logic [WIDTH-1:0]      Q,
  // internal DUT nets (bound hierarchically)
  input  logic [WIDTH-1:0]      sum,
  input  logic [WIDTH:0]        carry
);

  default clocking cb @(posedge clk); endclocking

  // Reference addition (zero carry-in)
  let ADD = {1'b0, A} + {1'b0, B};

  // Basic net sanity
  assert property (cb !$isunknown({Q,sum,carry})); // no X/Z on critical nets

  // Combinational ripple-carry correctness
  assert property (cb carry[0] == 1'b0);
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : g_bit
      assert property (cb sum[i] == (A[i] ^ B[i] ^ carry[i]));
      assert property (cb carry[i+1] == ((A[i]&B[i]) | (A[i]&carry[i]) | (B[i]&carry[i])));
    end
  endgenerate
  assert property (cb sum == ADD[WIDTH-1:0]);
  assert property (cb carry[WIDTH] == ADD[WIDTH]);

  // Sequential behavior of Q
  // Reset wins
  assert property (cb rst |=> (Q == '0));
  // Hold when not loading
  assert property (cb disable iff (rst) !load |=> (Q == $past(Q)));
  // Load captures A+B (truncated) from the load cycle
  assert property (cb disable iff (rst) load |=> (Q == $past(ADD[WIDTH-1:0])));

  // Coverage
  cover property (cb rst ##1 !rst);                               // reset deassertion
  cover property (cb !rst && load && (ADD[WIDTH] == 1'b1));       // overflow case
  cover property (cb !rst && load && (ADD[WIDTH] == 1'b0));       // no overflow
  cover property (cb !rst && !load ##1 !load);                    // hold path

endmodule

// Bind into DUT; accesses internal sum/carry
bind adder adder_sva #(.WIDTH(WIDTH)) u_adder_sva (
  .clk(clk), .rst(rst), .load(load),
  .A(A), .B(B), .Q(Q),
  .sum(sum), .carry(carry)
);
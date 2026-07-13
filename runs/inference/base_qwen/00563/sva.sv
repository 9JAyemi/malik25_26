module comparator_block_sva #(
  parameter n = 8 // number of bits in input signals
)(
  input [n-1:0] a,
  input [n-1:0] b,
  output gt,
  output lt,
  output eq
);

  wire [n:0] a_ext, b_ext;
  assign a_ext = {1'b0, a};
  assign b_ext = {1'b0, b};

  wire [n:0] a_gt_b, a_lt_b, a_eq_b;
  genvar i;
  generate
    for (i = 0; i <= n; i = i + 1) begin : compare_bits
      assign a_gt_b[i] = a_ext[i] & ~b_ext[i];
      assign a_lt_b[i] = ~a_ext[i] & b_ext[i];
      assign a_eq_b[i] = a_ext[i] == b_ext[i];
    end
  endgenerate

  assign gt = |a_gt_b;
  assign lt = |a_lt_b;
  assign eq = &a_eq_b;

  // a_gt_b[i] can only be set when a_ext[i] is 1 and b_ext[i] is 0
  bit_gt: assert property (
    @(posedge clk) disable iff (!reset_n) a_gt_b[i] |-> (a_ext[i] == 1'b1) && (b_ext[i] == 1'b0)
  );

  // a_lt_b[i] can only be set when a_ext[i] is 0 and b_ext[i] is 1
  bit_lt: assert property (
    @(posedge clk) disable iff (!reset_n) a_lt_b[i] |-> (a_ext[i] == 1'b0) && (b_ext[i] == 1'b1)
  );

  // a_eq_b[i] can only be set when a_ext[i] is equal to b_ext[i]
  bit_eq: assert property (
    @(posedge clk) disable iff (!reset_n) a_eq_b[i] |-> (a_ext[i] == b_ext[i])
  );

  // gt can only be set when at least one bit in a_gt_b is set
  gt_set: assert property (
    @(posedge clk) disable iff (!reset_n) gt |-> |a_gt_b
  );

  // lt can only be set when at least one bit in a_lt_b is set
  lt_set: assert property (
    @(posedge clk) disable iff (!reset_n) lt |-> |a_lt_b
  );

  // eq can only be set when all bits in a_eq_b are set
  eq_set: assert property (
    @(posedge clk) disable iff (!reset_n) eq |-> &a_eq_b
  );

  // gt and lt cannot both be set at the same time
  gt_lt_exclusive: assert property (
    @(posedge clk) disable iff (!reset_n) !(gt && lt)
  );

  // gt and eq cannot both be set at the same time
  gt_eq_exclusive: assert property (
    @(posedge clk) disable iff (!reset_n) !(gt && eq)
  );

  // lt and eq cannot both be set at the same time
  lt_eq_exclusive: assert property (
    @(posedge clk) disable iff (!reset_n) !(lt && eq)
  );

  // a_gt_b[i] and a_lt_b[i] cannot both be set at the same time
  bit_gt_lt_exclusive: assert property (
    @(posedge clk) disable iff (!reset_n) !(a_gt_b[i] && a_lt_b[i])
  );

  // a_gt_b[i] and a_eq_b[i] cannot both be set at the same time
  bit_gt_eq_exclusive: assert property (
    @(posedge clk) disable iff (!reset_n) !(a_gt_b[i] && a_eq_b[i])
  );

  // a_lt_b[i] and a_eq_b[i] cannot both be set at the same time
  bit_lt_eq_exclusive: assert property (
    @(posedge clk) disable iff (!reset_n) !(a_lt_b[i] && a_eq_b[i])
  );

endmodule
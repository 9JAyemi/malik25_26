module comparator_block #(
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

endmodule
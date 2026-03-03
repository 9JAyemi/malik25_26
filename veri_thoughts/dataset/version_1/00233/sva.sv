// SVA checker for comparator; bind this to the DUT. Provides concise but thorough checks and coverage.
module comparator_sva #(
  parameter int n = 4,
  parameter int s = 0
)(
  input  logic                   clk,
  input  logic                   rst_n,
  input  logic [n-1:0]           in1,
  input  logic [n-1:0]           in2,
  input  logic                   out
);

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Useful constants
  localparam logic [n-1:0] MAX_U = {n{1'b1}};
  localparam logic [n-1:0] MIN_U = '0;
  localparam logic [n-1:0] MIN_S = {1'b1, {(n-1){1'b0}}};
  localparam logic [n-1:0] MAX_S = {1'b0, {(n-1){1'b1}}};

  // Sanity: no X on output when inputs are known
  property p_no_x_out;
    !$isunknown({in1,in2}) |-> !$isunknown(out);
  endproperty
  assert property (p_no_x_out);

  // Equality must never assert 'greater-than'
  property p_eq_implies_zero;
    !$isunknown({in1,in2}) && (in1 == in2) |-> (out == 1'b0);
  endproperty
  assert property (p_eq_implies_zero);

  generate
    if (s == 0) begin : g_unsigned
      // Unsigned correctness
      property p_unsigned_correct;
        !$isunknown({in1,in2}) |-> (out === (in1 > in2));
      endproperty
      assert property (p_unsigned_correct);

      // Coverage (unsigned)
      cover property (!$isunknown({in1,in2}) && (in1 <  in2) && (out == 1'b0));
      cover property (!$isunknown({in1,in2}) && (in1 >  in2) && (out == 1'b1));
      cover property (!$isunknown({in1,in2}) && (in1 == in2) && (out == 1'b0));
      cover property (!$isunknown({in1,in2}) && (in1 == MAX_U) && (in2 == MIN_U) && (out == 1'b1));
      cover property (!$isunknown({in1,in2}) && (in1 == MIN_U) && (in2 == MAX_U) && (out == 1'b0));
    end
    else begin : g_signed
      // Signed correctness (reference check)
      property p_signed_correct;
        !$isunknown({in1,in2}) |-> (out === ($signed(in1) > $signed(in2)));
      endproperty
      assert property (p_signed_correct);

      // Decompose signed compare into explicit sign cases (helps pinpoint bugs)
      property p_sign_diff_rule;
        !$isunknown({in1,in2}) && (in1[n-1] ^ in2[n-1]) |-> (out == ~in1[n-1]);
      endproperty
      assert property (p_sign_diff_rule); // This will fail if DUT returns in1[n-1] instead of ~in1[n-1]

      property p_same_sign_rule;
        !$isunknown({in1,in2}) && (in1[n-1] == in2[n-1]) |-> (out === (in1 > in2));
      endproperty
      assert property (p_same_sign_rule);

      // Coverage (signed)
      cover property (!$isunknown({in1,in2}) && (in1[n-1]==0) && (in2[n-1]==1) && (out==1)); // + > -
      cover property (!$isunknown({in1,in2}) && (in1[n-1]==1) && (in2[n-1]==0) && (out==0)); // - !> +
      cover property (!$isunknown({in1,in2}) && (in1[n-1]==0) && (in2[n-1]==0) && (in1 > in2) && (out==1)); // + vs +
      cover property (!$isunknown({in1,in2}) && (in1[n-1]==1) && (in2[n-1]==1) && (in1 > in2) && (out==1)); // - vs -
      cover property (!$isunknown({in1,in2}) && (in1 == in2) && (out==0));                                // equal
      cover property (!$isunknown({in1,in2}) && (in1==MAX_S) && (in2==MIN_S) && (out==1));                // max_s > min_s
      cover property (!$isunknown({in1,in2}) && (in1==MIN_S) && (in2==MAX_S) && (out==0));                // min_s !> max_s
    end
  endgenerate

endmodule

// Example bind (from a testbench or top-level):
// bind comparator comparator_sva #(.n(n), .s(s)) u_cmp_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));
// SVA for parity_sum and parity_checker
// Concise, bound-in checkers with essential assertions and coverage

// Checker for parity_checker: verifies prefix-XOR chain and output parity
module parity_checker_sva #(
  parameter int DATAWIDTH = 8
) (
  input  logic [DATAWIDTH-1:0] data,
  input  logic [DATAWIDTH-1:0] sum,     // internal net of DUT (bound)
  input  logic                 parity
);

  // Parameter sanity
  initial assert (DATAWIDTH > 0);

  // No X on inputs/outputs/internals
  assert property (@(*)) !$isunknown({data, sum, parity});

  // Functional: prefix XOR chain and reduction parity
  generate
    if (DATAWIDTH > 0) begin
      // Base of prefix XOR
      assert property (@(*)) sum[0] == data[0];

      genvar i;
      for (i = 1; i < DATAWIDTH; i++) begin : g_chk
        // Recurrence form
        assert property (@(*)) sum[i] == (sum[i-1] ^ data[i]);
        // Direct reduction form
        assert property (@(*)) sum[i] == ^data[i:0];
      end

      // Output equals full reduction
      assert property (@(*)) parity == sum[DATAWIDTH-1];
      assert property (@(*)) parity == ^data;
    end
  endgenerate

  // Lightweight coverage
  cover property (@(*)) parity == 1'b0;
  cover property (@(*)) parity == 1'b1;
  cover property (@(*)) data == '0;
  cover property (@(*)) data == {DATAWIDTH{1'b1}};

endmodule

// Checker for parity_sum: assumes 9-bit arithmetic sum a+b
module parity_sum_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [8:0] parity_sum
);

  // No X on IOs
  assert property (@(*)) !$isunknown({a, b, parity_sum});

  // Functional: 9-bit combinational add
  assert property (@(*)) parity_sum == (a + b);

  // Coverage: zero, carry-out, and max
  cover property (@(*)) parity_sum == 9'd0;
  cover property (@(*)) parity_sum[8] == 1'b1;          // carry observed
  cover property (@(*)) parity_sum == 9'h1FF;           // max sum (255+255)

endmodule

// Bind checkers into DUTs (access internal 'sum' of parity_checker)
bind parity_checker parity_checker_sva #(.DATAWIDTH(DATAWIDTH))
  u_parity_checker_sva (
    .data   (data),
    .sum    (sum),
    .parity (parity)
  );

bind parity_sum parity_sum_sva
  u_parity_sum_sva (
    .a          (a),
    .b          (b),
    .parity_sum (parity_sum)
  );
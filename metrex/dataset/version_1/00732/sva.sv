// SVA for byte_sum_and_multiply
// Binds end-to-end functional equivalence and targeted coverage.

module byte_sum_and_multiply_sva (
  input  logic [15:0] in,
  input  logic [15:0] out
);

  // Main functional check (combinational, X-safe on inputs)
  always_comb begin
    logic [15:0] exp;
    exp = {8'd0, in[15:8]} + {8'd0, in[7:0]};
    exp = exp << 1;

    if (!$isunknown(in)) begin
      assert (out === exp)
        else $error("byte_sum_and_multiply: out mismatch. in=%0h out=%0h exp=%0h", in, out, exp);

      // Sanity implied by spec: result must be even (multiply by 2)
      assert (out[0] == 1'b0)
        else $error("byte_sum_and_multiply: LSB must be 0. in=%0h out=%0h", in, out);
    end
  end

  // Lightweight functional coverage
  always_comb begin
    logic [8:0] sum9;
    sum9 = in[15:8] + in[7:0];

    if (!$isunknown(in)) begin
      cover (in == 16'h0000);                    // both bytes zero
      cover (in == 16'hFFFF);                    // both bytes max
      cover (in[15:8]==8'hFF && in[7:0]==8'h00); // asymmetry
      cover (in[15:8]==8'h00 && in[7:0]==8'hFF); // asymmetry
      cover (sum9 == 9'd0);                      // sum zero
      cover (sum9 == 9'd255);                    // near max without carry
      cover (sum9 >= 9'd256);                    // carry from 8-bit add
      cover (({8'd0, sum9} << 1) == out);        // observe expected mapping
    end
  end

endmodule

bind byte_sum_and_multiply byte_sum_and_multiply_sva sva_inst (.in(in), .out(out));
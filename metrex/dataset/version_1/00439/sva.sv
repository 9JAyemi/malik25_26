// SVA for top_module and submodules (concise, quality-focused)
// Bind these modules to your DUTs as shown at the bottom.

module top_module_sva (
  input  logic [7:0] in1,
  input  logic [7:0] in2,
  input  logic [7:0] out,
  // internal taps from top_module
  input  logic [3:0] in1_hi, in1_lo,
  input  logic [3:0] in2_hi, in2_lo,
  input  logic [3:0] sum1, sum2,
  input  logic [7:0] out_sum
);
  always_comb begin
    // Split correctness
    assert (in1_hi == in1[7:4]) else $error("in1_hi mismatch exp=%0h got=%0h", in1[7:4], in1_hi);
    assert (in1_lo == in1[3:0]) else $error("in1_lo mismatch exp=%0h got=%0h", in1[3:0], in1_lo);
    assert (in2_hi == in2[7:4]) else $error("in2_hi mismatch exp=%0h got=%0h", in2[7:4], in2_hi);
    assert (in2_lo == in2[3:0]) else $error("in2_lo mismatch exp=%0h got=%0h", in2[3:0], in2_lo);

    // 4-bit adders modulo-16
    assert (sum1 == ((in1_hi + in2_hi) & 4'hF)) else
      $error("sum1 mismatch exp=%0h got=%0h", ((in1_hi + in2_hi) & 4'hF), sum1);
    assert (sum2 == ((in1_lo + in2_lo) & 4'hF)) else
      $error("sum2 mismatch exp=%0h got=%0h", ((in1_lo + in2_lo) & 4'hF), sum2);

    // 8-bit add pipeline
    assert (out_sum == ({4'b0, sum1} + {4'b0, sum2})) else
      $error("out_sum mismatch exp=%0h got=%0h", ({4'b0, sum1} + {4'b0, sum2}), out_sum);

    // Divide-by-4 behavior
    assert (out == (out_sum >> 2)) else
      $error("out mismatch vs out_sum>>2 exp=%0h got=%0h", (out_sum >> 2), out);

    // Strong end-to-end functional check from inputs only
    automatic logic [3:0] s1 = (in1[7:4] + in2[7:4]) & 4'hF;
    automatic logic [3:0] s2 = (in1[3:0] + in2[3:0]) & 4'hF;
    automatic logic [7:0] exp_out = ({4'b0, s1} + {4'b0, s2}) >> 2;
    assert (out == exp_out) else
      $error("end-to-end out mismatch exp=%0h got=%0h", exp_out, out);

    // Consequence of >>2 (MSB must be 0)
    assert (out[7] == 1'b0) else $error("out[7] must be 0 after >>2");

    // Lightweight functional coverage
    cover ((({1'b0,in1[7:4]} + {1'b0,in2[7:4]}) > 5'd15)); // hi-nibble overflow
    cover ((({1'b0,in1[3:0]} + {1'b0,in2[3:0]}) > 5'd15)); // lo-nibble overflow
    cover (out_sum == 8'd0);
    cover (out_sum == 8'd30); // max possible (15+15)
    cover (out_sum[1:0] != 2'b00); // shift has visible effect
  end
endmodule

module adder_4bit_sva (
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic [3:0] sum
);
  always_comb begin
    assert (sum == ((in1 + in2) & 4'hF)) else
      $error("adder_4bit sum mismatch exp=%0h got=%0h", ((in1 + in2) & 4'hF), sum);
    cover (({1'b0,in1} + {1'b0,in2}) > 5'd15); // overflow case observed
    cover (sum == 4'h0);
    cover (sum == 4'hF);
  end
endmodule

module adder_8bit_sva (
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [7:0] sum
);
  always_comb begin
    assert (sum == (in1 + in2)) else
      $error("adder_8bit sum mismatch exp=%0h got=%0h", (in1 + in2), sum);
    cover (sum == 8'h00);
    cover (sum == 8'hFF);
  end
endmodule

module split_1_4bit_sva (
  input logic [7:0] in,
  input logic [3:0] hi,
  input logic [3:0] lo
);
  always_comb begin
    assert (hi == in[7:4]) else $error("split hi mismatch exp=%0h got=%0h", in[7:4], hi);
    assert (lo == in[3:0]) else $error("split lo mismatch exp=%0h got=%0h", in[3:0], lo);
    cover (in == 8'h00);
    cover (in == 8'hFF);
  end
endmodule

// Example bind statements (adjust instance names as needed):
// bind top_module   top_module_sva   u_top_sva(.*,
//   .in1_hi(in1_hi), .in1_lo(in1_lo), .in2_hi(in2_hi), .in2_lo(in2_lo),
//   .sum1(sum1), .sum2(sum2), .out_sum(out_sum));
// bind adder_4bit   adder_4bit_sva   u_a4_sva(.*);
// bind adder_8bit   adder_8bit_sva   u_a8_sva(.*);
// bind split_1_4bit split_1_4bit_sva u_split_sva(.*);
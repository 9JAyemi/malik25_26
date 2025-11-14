// SVA for the provided combinational design.
// Uses immediate assertions/cover in always_comb (no clock in DUT).

// ---------- Common helper functions ----------
package top_sva_pkg;
  function automatic [7:0] add8(input [7:0] x, input [7:0] y);
    add8 = (x + y); // 8-bit wrap
  endfunction

  function automatic [31:0] byte_add32(input [31:0] a, input [31:0] b);
    byte_add32 = { add8(a[31:24], b[31:24]),
                   add8(a[23:16], b[23:16]),
                   add8(a[15:8] , b[15:8] ),
                   add8(a[7:0]  , b[7:0]  ) };
  endfunction

  function automatic [31:0] rev32(input [31:0] x);
    rev32 = { x[7:0], x[15:8], x[23:16], x[31:24] };
  endfunction
endpackage

// ---------- top_module SVA ----------
module top_module_sva(
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [31:0] out,
  input  logic [31:0] adder_output
);
  import top_sva_pkg::*;
  always_comb begin
    automatic logic [31:0] exp_sum = byte_add32(a,b);
    automatic logic [31:0] exp_out = rev32(exp_sum);

    // Functional composition
    assert (adder_output == exp_sum)
      else $error("top: adder_output mismatch exp_sum");
    assert (out == exp_out)
      else $error("top: out mismatch exp_out");
    assert (out == rev32(adder_output))
      else $error("top: out != byte_reverse(adder_output)");

    // Known-ness
    if (!$isunknown({a,b})) assert (!$isunknown(out))
      else $error("top: out has X/Z with known inputs");

    // Targeted coverage
    cover (({1'b0,a[7:0]}   + {1'b0,b[7:0]}  )[8]);  // byte0 overflow
    cover (({1'b0,a[15:8]}  + {1'b0,b[15:8]} )[8]);  // byte1 overflow
    cover (({1'b0,a[23:16]} + {1'b0,b[23:16]})[8]);  // byte2 overflow
    cover (({1'b0,a[31:24]} + {1'b0,b[31:24]})[8]);  // byte3 overflow
    cover (&({({1'b0,a[7:0]}   + {1'b0,b[7:0]}  )[8],
              ({1'b0,a[15:8]}  + {1'b0,b[15:8]} )[8],
              ({1'b0,a[23:16]} + {1'b0,b[23:16]})[8],
              ({1'b0,a[31:24]} + {1'b0,b[31:24]})[8]})); // all bytes overflow
    cover (out == 32'h0000_0000);
    cover (out == 32'hFFFF_FFFF);
  end
endmodule

bind top_module top_module_sva i_top_module_sva(
  .a(a), .b(b), .out(out), .adder_output(adder_output)
);

// ---------- adder_32bit SVA ----------
module adder_32bit_sva(
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [31:0] sum,
  input  logic [7:0]  adder_output_0,
  input  logic [7:0]  adder_output_1,
  input  logic [7:0]  adder_output_2,
  input  logic [7:0]  adder_output_3
);
  import top_sva_pkg::*;
  always_comb begin
    // Sub-lane correctness
    assert (adder_output_0 == a[7:0]   + b[7:0])
      else $error("adder32: lane0 mismatch");
    assert (adder_output_1 == a[15:8]  + b[15:8])
      else $error("adder32: lane1 mismatch");
    assert (adder_output_2 == a[23:16] + b[23:16])
      else $error("adder32: lane2 mismatch");
    assert (adder_output_3 == a[31:24] + b[31:24])
      else $error("adder32: lane3 mismatch");

    // Concatenation and overall function
    assert (sum == {adder_output_3,adder_output_2,adder_output_1,adder_output_0})
      else $error("adder32: sum concatenation mismatch");
    assert (sum == byte_add32(a,b))
      else $error("adder32: sum != bytewise a+b");

    // Known-ness
    if (!$isunknown({a,b})) assert (!$isunknown(sum))
      else $error("adder32: sum has X/Z with known inputs");

    // Coverage
    cover (({1'b0,a[7:0]}   + {1'b0,b[7:0]}  )[8]);
    cover (({1'b0,a[15:8]}  + {1'b0,b[15:8]} )[8]);
    cover (({1'b0,a[23:16]} + {1'b0,b[23:16]})[8]);
    cover (({1'b0,a[31:24]} + {1'b0,b[31:24]})[8]);
    cover (sum == 32'h0000_0000);
    cover (sum == 32'hFFFF_FFFF);
  end
endmodule

bind adder_32bit adder_32bit_sva i_adder_32bit_sva(
  .a(a), .b(b), .sum(sum),
  .adder_output_0(adder_output_0),
  .adder_output_1(adder_output_1),
  .adder_output_2(adder_output_2),
  .adder_output_3(adder_output_3)
);

// ---------- adder_8bit SVA ----------
module adder_8bit_sva(
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] sum
);
  always_comb begin
    assert (sum == a + b)
      else $error("adder8: sum != a+b (8-bit wrap)");

    if (!$isunknown({a,b})) assert (!$isunknown(sum))
      else $error("adder8: sum has X/Z with known inputs");

    // Coverage
    automatic logic [8:0] t = {1'b0,a} + {1'b0,b};
    cover (t[8]);             // overflow
    cover (sum == 8'h00);
    cover (sum == 8'hFF);
  end
endmodule

bind adder_8bit adder_8bit_sva i_adder_8bit_sva(.a(a), .b(b), .sum(sum));

// ---------- byte_reverser SVA ----------
module byte_reverser_sva(
  input  logic [31:0] input_data,
  input  logic [31:0] output_data
);
  import top_sva_pkg::*;
  always_comb begin
    assert (output_data == rev32(input_data))
      else $error("reverser: output_data != reversed input_data");

    if (!$isunknown(input_data)) assert (!$isunknown(output_data))
      else $error("reverser: output_data has X/Z with known input_data");

    // Coverage
    cover (input_data == 32'h0102_0304); // exercise a non-palindromic pattern
  end
endmodule

bind byte_reverser byte_reverser_sva i_byte_reverser_sva(
  .input_data(input_data), .output_data(output_data)
);
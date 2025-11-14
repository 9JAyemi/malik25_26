// SVA checker for top_module (combinational). Bind this to the DUT.
// Focuses on correctness of internal wiring, arithmetic, and overflow path.

`ifndef TOP_MODULE_SVA_SV
`define TOP_MODULE_SVA_SV

module top_module_sva (
    input [7:0] a,
    input [7:0] b,
    input [7:0] s,
    input       overflow,
    input [7:0] final_output,

    // Internals
    input [15:0] product,
    input [8:0]  sum,
    input        msb_in_a, msb_in_b, msb_out,
    input [8:0]  product_1,
    input [8:0]  product_2,
    input [8:0]  product_3,
    input [8:0]  product_4,
    input [8:0]  product_5,
    input [8:0]  product_6,
    input [8:0]  product_7,
    input [8:0]  product_8
);

  // Basic internal correctness and arithmetic relationships
  always_comb begin
    // msb taps
    assert (msb_in_a == a[7]) else $error("msb_in_a != a[7]");
    assert (msb_in_b == b[7]) else $error("msb_in_b != b[7]");

    // Each partial product is 9b with only bit[0] potentially 1, equals a[7]&b[i]
    assert (product_1[8:1] == '0 && product_1[0] == (a[7] & b[0])) else $error("product_1 mismatch");
    assert (product_2[8:1] == '0 && product_2[0] == (a[7] & b[1])) else $error("product_2 mismatch");
    assert (product_3[8:1] == '0 && product_3[0] == (a[7] & b[2])) else $error("product_3 mismatch");
    assert (product_4[8:1] == '0 && product_4[0] == (a[7] & b[3])) else $error("product_4 mismatch");
    assert (product_5[8:1] == '0 && product_5[0] == (a[7] & b[4])) else $error("product_5 mismatch");
    assert (product_6[8:1] == '0 && product_6[0] == (a[7] & b[5])) else $error("product_6 mismatch");
    assert (product_7[8:1] == '0 && product_7[0] == (a[7] & b[6])) else $error("product_7 mismatch");
    assert (product_8[8:1] == '0 && product_8[0] == (a[7] & b[7])) else $error("product_8 mismatch");

    // Truncation behavior of the 72b concatenation into 16b product
    assert (product == {product_8,product_7,product_6,product_5,product_4,product_3,product_2,product_1})
      else $error("product concat mismatch");
    assert (product[7:0]  == product_1[7:0]) else $error("product[7:0] mismatch");
    assert (product[15:8] == product_2[7:0]) else $error("product[15:8] mismatch");

    // Sum and slice outputs
    assert (sum == product[7:0] + product[15:8]) else $error("sum mismatch");
    assert (s == sum[7:0]) else $error("s != sum[7:0]");
    assert (msb_out == sum[8]) else $error("msb_out != sum[8]");

    // Overflow logic as implemented
    assert (overflow == ((msb_in_a == msb_in_b) && (msb_in_a != msb_out)))
      else $error("overflow logic mismatch");

    // Output of overflow_detector
    assert (final_output == sum[7:0]) else $error("final_output != sum[7:0]");
    assert (final_output == s) else $error("final_output != s");

    // Given structure, no carry to bit[8] in sum (8b + 8b with only LSBs possibly 1)
    assert (sum[8] == 1'b0) else $error("Unexpected carry in sum[8]");
    assert (sum[7:2] == '0) else $error("Unexpected upper bits set in sum[7:2]");
  end

  // Minimal functional coverage (combinational immediate cover)
  always_comb begin
    // Partial products activation
    cover (product_1[0]);
    cover (product_2[0]);
    cover (product_1[0] && product_2[0]);

    // Sum result space driven by the two LSBs
    cover (sum == 9'd0);
    cover (sum == 9'd1);
    cover (sum == 9'd2);

    // Sign combinations and overflow visibility
    cover (msb_in_a ^ msb_in_b);
    cover (msb_in_a & msb_in_b);
    cover (!msb_in_a & !msb_in_b);
    cover (overflow);
    cover (!overflow);
  end

endmodule

// Bind into the DUT so all internal nets are visible by name
bind top_module top_module_sva top_module_sva_i (.*);

`endif
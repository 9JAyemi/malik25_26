// SystemVerilog Assertions (SVA) for top_module, decoder_module, xor_module
// Focused, high-quality checks with concise functional coverage

// ---------------- top_module SVA ----------------
module top_module_sva (
  input  logic [2:0] a,
  input  logic [2:0] b,
  input  logic [2:0] out_or_bitwise,
  input  logic       out_or_logical,
  input  logic [5:0] out_not
);
  // Combinational equivalence and X-prop checks
  always_comb begin
    if (!$isunknown({a,b})) begin
      assert (out_or_bitwise == (a | b))
        else $error("out_or_bitwise != (a|b)");
      assert (out_or_logical == (a[0] ^ b[0]))
        else $error("out_or_logical != (a[0]^b[0])");
      assert (out_not == {~b, ~a})
        else $error("out_not != {~b,~a}");
      assert (!$isunknown({out_or_bitwise,out_or_logical,out_not}))
        else $error("Outputs contain X/Z with known inputs");
    end
  end

  // Functional coverage (concise but meaningful)
  // Cover all possible values seen on out_or_bitwise
  genvar i;
  generate
    for (i=0; i<8; i++) begin: COV_OR_VALS
      cover property (@(a or b) out_or_bitwise == i[2:0]);
    end
  endgenerate

  // Cover both values for the 1-bit logical output
  cover property (@(a or b) out_or_logical == 1'b0);
  cover property (@(a or b) out_or_logical == 1'b1);

  // Cover all possible values on each 3-bit half of out_not
  genvar j;
  generate
    for (j=0; j<8; j++) begin: COV_NOT_HALVES
      cover property (@(a or b) out_not[2:0] == j[2:0]); // ~a
      cover property (@(a or b) out_not[5:3] == j[2:0]); // ~b
    end
  endgenerate
endmodule

bind top_module top_module_sva (
  .a(a), .b(b),
  .out_or_bitwise(out_or_bitwise),
  .out_or_logical(out_or_logical),
  .out_not(out_not)
);

// ---------------- decoder_module SVA ----------------
module decoder_module_sva (
  input  logic [2:0] in,
  input  logic [7:0] out
);
  // Equivalence to 1<<in when input is known; onehot guarantee
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out == (8'b1 << in))
        else $error("decoder out != 1<<in");
      assert ($onehot(out))
        else $error("decoder out is not one-hot");
    end
  end

  // Cover every code point
  genvar k;
  generate
    for (k=0; k<8; k++) begin: COV_DEC
      cover property (@(in) (in == k[2:0]) and (out == (8'b1 << k)));
    end
  endgenerate
endmodule

bind decoder_module decoder_module_sva (.in(in), .out(out));

// ---------------- xor_module SVA ----------------
module xor_module_sva (
  input  logic a,
  input  logic b,
  input  logic out
);
  // Combinational equivalence and full 2-bit input space coverage
  always_comb begin
    assert (out === (a ^ b))
      else $error("xor_module out != a^b");
  end

  cover property (@(a or b) a==1'b0 && b==1'b0 && out==1'b0);
  cover property (@(a or b) a==1'b0 && b==1'b1 && out==1'b1);
  cover property (@(a or b) a==1'b1 && b==1'b0 && out==1'b1);
  cover property (@(a or b) a==1'b1 && b==1'b1 && out==1'b0);
endmodule

bind xor_module xor_module_sva (.a(a), .b(b), .out(out));
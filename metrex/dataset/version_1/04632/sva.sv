// SVA for addsub: concise checks and targeted coverage
module addsub_sva #(parameter int W=4)
(
  input  logic [W-1:0] A,
  input  logic [W-1:0] B,
  input  logic         subtract,
  input  logic [W-1:0] result,
  // bind to internal DUT wires for deeper checking
  input  logic [W-1:0] B_neg,
  input  logic [W-1:0] temp_result
);

  logic [W-1:0] two_comp_B;
  logic [W-1:0] golden;

  always_comb begin
    two_comp_B = ~B + {{(W-1){1'b0}},1'b1};
    golden     = A + (subtract ? two_comp_B : B);

    // Sanity/X checks
    if (!$isunknown({A,B,subtract})) begin
      assert (B_neg == two_comp_B)
        else $error("B_neg mismatch: exp=%0h got=%0h", two_comp_B, B_neg);

      // Internal correctness
      assert (temp_result == golden)
        else $error("temp_result mismatch: exp=%0h got=%0h", golden, temp_result);

      // Final functional spec (this will flag the double-add bug)
      assert (result == golden)
        else $error("result mismatch: exp=%0h got=%0h", golden, result);

      // No X/Z on outputs when inputs are known
      assert (!$isunknown({B_neg,temp_result,result}))
        else $error("X/Z detected on outputs");
    end

    // Targeted functional coverage
    cover (!subtract);                      // add operation hit
    cover ( subtract);                      // subtract operation hit
    cover (!subtract && ({1'b0,A}+{1'b0,B})[W]); // add overflow (carry-out)
    cover ( subtract && (A < B));           // subtract borrow case
    cover (A=={W{1'b0}}); cover (B=={W{1'b0}});
    cover (A=={W{1'b1}}); cover (B=={W{1'b1}});
  end

endmodule

// Bind into the DUT
bind addsub addsub_sva #(.W(4)) addsub_sva_i (.*);
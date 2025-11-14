// SVA checker for parity_generator_checker
// - Asserts combinational correctness and X safety
// - Provides simple functional coverage
module parity_generator_checker_sva #(parameter string parity_type = "even")
(
  input  logic [7:0] data_in,
  input  logic       parity_in,
  input  logic       parity_out,
  input  logic       correct
);

  // Parameter validity
  initial begin
    assert (parity_type == "even" || parity_type == "odd")
      else $error("parity_type must be \"even\" or \"odd\", got \"%s\"", parity_type);
  end

  // Combinational functional checks and coverage
  always_comb begin
    automatic bit   inputs_known = !$isunknown({data_in, parity_in});
    automatic logic exp_parity   = (parity_type == "even") ? ^data_in : ~^data_in;

    if (inputs_known) begin
      // Outputs must be known with known inputs
      assert (!$isunknown({parity_out, correct}))
        else $error("Outputs X/Z with known inputs: data_in=%0h parity_in=%b", data_in, parity_in);

      // Parity generation correctness
      assert (parity_out === exp_parity)
        else $error("parity_out mismatch: exp=%b got=%b data_in=%0h", exp_parity, parity_out, data_in);

      // Checker correctness (both by spec and by output relation)
      assert (correct === (parity_in === exp_parity))
        else $error("correct mismatch (spec): exp=%b got=%b data_in=%0h parity_in=%b",
                    (parity_in===exp_parity), correct, data_in, parity_in);

      assert (correct === (parity_in === parity_out))
        else $error("correct mismatch (consistency): data_in=%0h parity_in=%b parity_out=%b correct=%b",
                    data_in, parity_in, parity_out, correct);

      // Minimal functional coverage
      cover (parity_out == 0);
      cover (parity_out == 1);
      cover (correct == 0);
      cover (correct == 1);
      cover (parity_in == exp_parity && correct);
      cover (parity_in != exp_parity && !correct);
    end
  end

endmodule

// Bind into the DUT
bind parity_generator_checker
  parity_generator_checker_sva #(.parity_type(parity_type)) pgc_sva (.*);
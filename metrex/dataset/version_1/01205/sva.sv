// SVA checker for sum_4bit
module sum_4bit_sva(input logic [3:0] input_a, input logic [4:0] output_sum);

  // Combinational correctness and carry check; guard against unknown inputs
  always @* begin
    if (!$isunknown(input_a)) begin
      assert (output_sum == {1'b0, input_a} + 5'd1)
        else $error("sum_4bit: output_sum != input_a+1 (in=%0h out=%0h)", input_a, output_sum);
      assert (output_sum[4] == &input_a)
        else $error("sum_4bit: carry_out incorrect (in=%0h out=%0h)", input_a, output_sum);
      assert (!$isunknown(output_sum))
        else $error("sum_4bit: output_sum has X/Z with known input_a (in=%0h out=%0h)", input_a, output_sum);
    end
  end

  // Functional coverage: hit every input value with correct sum
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov
      always @* cover (!$isunknown(input_a) &&
                       input_a == i[3:0] &&
                       output_sum == {1'b0, i[3:0]} + 5'd1);
    end
  endgenerate

endmodule

// Bind the checker to the DUT
bind sum_4bit sum_4bit_sva u_sum_4bit_sva(.input_a(input_a), .output_sum(output_sum));
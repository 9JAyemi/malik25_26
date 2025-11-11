// SVA bind file for value_converter
module value_converter_sva(input [3:0] input_val, input [2:0] output_val);

  function automatic [2:0] exp(input [3:0] in);
    exp = ((in==4'd5)||(in==4'd6)) ? 3'd7 : in[2:0];
  endfunction

  // Functional correctness and X/Z checks (combinational)
  always_comb begin
    if (!$isunknown(input_val)) begin
      assert (output_val === exp(input_val))
        else $error("value_converter mismatch: in=%0d out=%0d exp=%0d", input_val, output_val, exp(input_val));
      assert (!$isunknown(output_val))
        else $error("value_converter X/Z on output for in=%0d", input_val);
    end
  end

  // Targeted coverage
  always_comb begin
    // Special-case overrides
    cover (input_val==4'd5 && output_val==3'd7);
    cover (input_val==4'd6 && output_val==3'd7);
    // Default path to 7 to distinguish both ways to 7
    cover (input_val==4'd7 && output_val==3'd7);
    // Hit each possible output value
    cover (output_val==3'd0);
    cover (output_val==3'd1);
    cover (output_val==3'd2);
    cover (output_val==3'd3);
    cover (output_val==3'd4);
    cover (output_val==3'd5);
    cover (output_val==3'd6);
    cover (output_val==3'd7);
  end

endmodule

bind value_converter value_converter_sva sva_inst (.*);
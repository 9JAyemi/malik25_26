// SVA checker for gray_code_conversion
module gray_code_conversion_sva (
  input  logic [3:0] bin_input,
  input  logic [1:0] gray_output,
  input  logic       valid
);

  // Golden model
  function automatic logic [1:0] exp_gray (input logic [3:0] b);
    case (b)
      4'b0000: exp_gray = 2'b00;
      4'b0001: exp_gray = 2'b01;
      4'b0010: exp_gray = 2'b11;
      4'b0011: exp_gray = 2'b10;
      4'b0100: exp_gray = 2'b11;
      4'b0101: exp_gray = 2'b10;
      4'b0110: exp_gray = 2'b00;
      4'b0111: exp_gray = 2'b01;
      4'b1000: exp_gray = 2'b10;
      4'b1001: exp_gray = 2'b11;
      4'b1010: exp_gray = 2'b01;
      4'b1011: exp_gray = 2'b00;
      4'b1100: exp_gray = 2'b01;
      4'b1101: exp_gray = 2'b00;
      4'b1110: exp_gray = 2'b10;
      4'b1111: exp_gray = 2'b11;
      default: exp_gray = 2'b00;
    endcase
  endfunction

  function automatic logic exp_valid (input logic [3:0] b);
    return (b==4'b0000 || b==4'b0001 || b==4'b0011 || b==4'b0111 || b==4'b1111);
  endfunction

  // Core functional checks (combinational, level-sensitive)
  ap_func:      assert property ( !$isunknown(bin_input) |-> (gray_output == exp_gray(bin_input) && valid == exp_valid(bin_input)) )
                 else $error("gray_output/valid mismatch for bin_input=%b", bin_input);

  ap_no_x_out:  assert property ( !$isunknown(bin_input) |-> !$isunknown({gray_output,valid}) )
                 else $error("X/Z on outputs for known bin_input=%b", bin_input);

  ap_gray_legal: assert property ( gray_output inside {2'b00,2'b01,2'b10,2'b11} )
                  else $error("Illegal gray_output=%b", gray_output);

  ap_valid_2st:  assert property ( !$isunknown(valid) )
                  else $error("valid is X/Z");

  // Coverage: all inputs hit with correct outputs; all outputs/valid states seen
  genvar i;
  generate
    for (i=0;i<16;i++) begin : cov_inputs
      localparam logic [3:0] B = i[3:0];
      cover property (bin_input == B && gray_output == exp_gray(B) && valid == exp_valid(B));
    end
  endgenerate

  cover property (gray_output == 2'b00);
  cover property (gray_output == 2'b01);
  cover property (gray_output == 2'b10);
  cover property (gray_output == 2'b11);
  cover property (valid);
  cover property (!valid);

endmodule

// Bind into DUT
bind gray_code_conversion gray_code_conversion_sva sva_i (
  .bin_input  (bin_input),
  .gray_output(gray_output),
  .valid      (valid)
);
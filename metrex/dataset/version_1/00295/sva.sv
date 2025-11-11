// SVA for bin2gray. Bind this to the DUT instance.
// bind bin2gray bin2gray_sva u_bin2gray_sva(.bin(bin), .gray(gray));

module bin2gray_sva (
  input logic [3:0] bin,
  input logic [3:0] gray
);

  // Functional correctness for all inputs
  property p_gray_func;
    @(*) disable iff ($isunknown(bin))
      gray == {bin[3], bin[3]^bin[2], bin[2]^bin[1], bin[1]^bin[0]};
  endproperty
  a_gray_func: assert property (p_gray_func);

  // No X/Z on output when input is known
  a_no_x_on_gray: assert property (@(*) (!$isunknown(bin)) |-> !$isunknown(gray));

  // Adjacent-step behavior: if bin steps by +/-1, Gray must toggle exactly one bit
  property p_adjacent_step_onebit;
    @(*) disable iff ($isunknown({bin,$past(bin)}))
      ($changed(bin) && ((bin == $past(bin)+1) || ($past(bin) == bin+1)))
      |-> $onehot(gray ^ $past(gray));
  endproperty
  a_adjacent_step_onebit: assert property (p_adjacent_step_onebit);

  // Coverage: observe every input value with correct output
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cg_all_inputs
      localparam logic [3:0] B = i[3:0];
      localparam logic [3:0] G = {B[3], B[3]^B[2], B[2]^B[1], B[1]^B[0]};
      cover property (@(*) (bin == B) && (gray == G));
    end
  endgenerate

  // Coverage: see at least one +1 and -1 step with 1-bit Gray change
  cover property (@(*) (!$isunknown({bin,$past(bin)})) &&
                  (bin == $past(bin)+1) && $onehot(gray ^ $past(gray)));
  cover property (@(*) (!$isunknown({bin,$past(bin)})) &&
                  ($past(bin) == bin+1) && $onehot(gray ^ $past(gray)));

endmodule
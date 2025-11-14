// SVA checker for controllerHdl_Complex_Multiply
module controllerHdl_Complex_Multiply_sva (
  input  signed [17:0] In1_re,
  input  signed [17:0] In1_im,
  input  signed [17:0] In2_re,
  input  signed [17:0] In2_im,
  input  signed [35:0] Re,
  input  signed [35:0] Im,
  // internal nets
  input  signed [35:0] Product_out1,
  input  signed [35:0] Product1_out1,
  input  signed [35:0] Add1_out1,
  input  signed [35:0] Product2_out1,
  input  signed [35:0] Product3_out1,
  input  signed [35:0] Add2_out1
);
  default clocking cb @(*); endclocking
  default disable iff ($isunknown({In1_re,In1_im,In2_re,In2_im}));

  let mul_ar = $signed(In1_re) * $signed(In2_re);
  let mul_bi = $signed(In1_im) * $signed(In2_im);
  let mul_ai = $signed(In1_re) * $signed(In2_im);
  let mul_ib = $signed(In1_im) * $signed(In2_re);
  let spec_re = $signed(mul_ar) - $signed(mul_bi);
  let spec_im = $signed(mul_ai) + $signed(mul_ib);
  let sx18 = function automatic signed [35:0] (input signed [17:0] x); sx18 = {{18{x[17]}}, x}; endfunction

  // No X/Z on outputs when inputs are known
  assert property (!$isunknown({Re,Im}));

  // Top-level spec checks
  assert property ($signed(Re) == $signed(spec_re));
  assert property ($signed(Im) == $signed(spec_im));

  // Internal structural consistency
  assert property ($signed(Product_out1)  == $signed(mul_ar));
  assert property ($signed(Product1_out1) == $signed(mul_bi));
  assert property ($signed(Product2_out1) == $signed(mul_ai));
  assert property ($signed(Product3_out1) == $signed(mul_ib));
  assert property ($signed(Add1_out1) == $signed(Product_out1) - $signed(Product1_out1));
  assert property ($signed(Add2_out1) == $signed(Product2_out1) + $signed(Product3_out1));
  assert property ($signed(Re) == $signed(Add1_out1));
  assert property ($signed(Im) == $signed(Add2_out1));

  // Coverage: identities and corner cases
  cover property (In2_re==18'sd0 && In2_im==18'sd0 && Re==36'sd0 && Im==36'sd0);
  cover property (In2_re==18'sd1 && In2_im==18'sd0 && Re==$signed(sx18(In1_re)) && Im==$signed(sx18(In1_im)));
  cover property (In2_re==-18'sd1 && In2_im==18'sd0 && Re==$signed(-sx18(In1_re)) && Im==$signed(-sx18(In1_im)));
  cover property (In2_re==18'sd0 && In2_im==18'sd1 && Re==$signed(-sx18(In1_im)) && Im==$signed(sx18(In1_re)));
  cover property (In2_re==18'sd0 && In2_im==-18'sd1 && Re==$signed(sx18(In1_im)) && Im==$signed(-sx18(In1_re)));

  // Extremes on inputs
  cover property (In1_re==18'sd131071 || In1_re==-18'sd131072);
  cover property (In1_im==18'sd131071 || In1_im==-18'sd131072);
  cover property (In2_re==18'sd131071 || In2_re==-18'sd131072);
  cover property (In2_im==18'sd131071 || In2_im==-18'sd131072);

  // Cover add/sub overflow scenarios
  cover property ( ($signed(Product2_out1[35]) == $signed(Product3_out1[35])) &&
                   ($signed(Add2_out1[35]) != $signed(Product2_out1[35])) );
  cover property ( ($signed(Product_out1[35]) != $signed(Product1_out1[35])) &&
                   ($signed(Add1_out1[35]) != $signed(Product_out1[35])) );

  // Zero real/imag result with non-zero inputs
  cover property (Re==36'sd0 && {In1_re,In1_im,In2_re,In2_im}!=72'sd0);
  cover property (Im==36'sd0 && {In1_re,In1_im,In2_re,In2_im}!=72'sd0);
endmodule

bind controllerHdl_Complex_Multiply controllerHdl_Complex_Multiply_sva sva_i (
  .In1_re(In1_re),
  .In1_im(In1_im),
  .In2_re(In2_re),
  .In2_im(In2_im),
  .Re(Re),
  .Im(Im),
  .Product_out1(Product_out1),
  .Product1_out1(Product1_out1),
  .Add1_out1(Add1_out1),
  .Product2_out1(Product2_out1),
  .Product3_out1(Product3_out1),
  .Add2_out1(Add2_out1)
);
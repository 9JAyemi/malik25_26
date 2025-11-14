// SVA checker for complexMultiply. Bind to DUT instance.
// Clockless, event-driven on input changes; uses ##0 to sample post-update.

module complexMultiply_sva (
  input  signed [17:0] in1_re,
  input  signed [17:0] in1_im,
  input  signed [17:0] in2_re,
  input  signed [17:0] in2_im,
  input  signed [35:0] re,
  input  signed [35:0] im
);
  default clocking cb @ (in1_re or in1_im or in2_re or in2_im); endclocking

  function automatic signed [35:0] mul18x18(input signed [17:0] a, b);
    return $signed(a) * $signed(b);
  endfunction

  // Reference model
  logic signed [35:0] re_ref, im_ref;
  always_comb begin
    re_ref = mul18x18(in1_re,in2_re) - mul18x18(in1_im,in2_im);
    im_ref = mul18x18(in1_re,in2_im) + mul18x18(in1_im,in2_re);
  end

  // Correctness of outputs
  a_re_correct: assert property (##0 (re == re_ref));
  a_im_correct: assert property (##0 (im == im_ref));

  // Commutativity: (a+jb)*(c+jd) == (c+jd)*(a+jb)
  logic signed [35:0] re_comm, im_comm;
  always_comb begin
    re_comm = mul18x18(in2_re,in1_re) - mul18x18(in2_im,in1_im);
    im_comm = mul18x18(in2_re,in1_im) + mul18x18(in2_im,in1_re);
  end
  a_comm: assert property (##0 (re == re_comm && im == im_comm));

  // No X/Z propagation: known inputs => known outputs
  a_no_x: assert property (!$isunknown({in1_re,in1_im,in2_re,in2_im})) |-> ##0 (!$isunknown({re,im}));

  // Zero multiplicative annihilator
  a_zero: assert property (((in1_re==0 && in1_im==0) || (in2_re==0 && in2_im==0)) |-> ##0 (re==0 && im==0));

  // Overflow detection on final add/sub (36->37-bit extend and check sign consistency)
  function automatic signed [36:0] zext1(input signed [35:0] x); return {1'b0,x}; endfunction
  logic signed [36:0] re37, im37;
  always_comb begin
    re37 = $signed(zext1(mul18x18(in1_re,in2_re))) - $signed(zext1(mul18x18(in1_im,in2_im)));
    im37 = $signed(zext1(mul18x18(in1_re,in2_im))) + $signed(zext1(mul18x18(in1_im,in2_re)));
  end
  wire re_ovf = re37[36] ^ re37[35];
  wire im_ovf = im37[36] ^ im37[35];

  // Optional assertion (uncomment to enforce no overflow)
  // a_no_ovf: assert property (##0 (!re_ovf && !im_ovf));

  // Functional coverage (key scenarios)
  localparam signed [17:0] S18_MIN = -18'sd131072;
  localparam signed [17:0] S18_MAX =  18'sd131071;

  c_zero      : cover property (##0 ((in1_re==0 && in1_im==0) || (in2_re==0 && in2_im==0)));
  c_pure_real : cover property (##0 (in1_im==0 && in2_im==0));
  c_pure_imag : cover property (##0 (in1_re==0 && in2_re==0));
  c_conjugate : cover property (##0 (in2_re==in1_re && in2_im==-in1_im));
  c_ext_i1_re : cover property (##0 (in1_re==S18_MIN || in1_re==S18_MAX));
  c_ext_i1_im : cover property (##0 (in1_im==S18_MIN || in1_im==S18_MAX));
  c_ext_i2_re : cover property (##0 (in2_re==S18_MIN || in2_re==S18_MAX));
  c_ext_i2_im : cover property (##0 (in2_im==S18_MIN || in2_im==S18_MAX));
  c_re_ovf    : cover property (##0 re_ovf);
  c_im_ovf    : cover property (##0 im_ovf);
endmodule

bind complexMultiply complexMultiply_sva cm_sva_bind (.*);
// SVA for FP16RMulS0Of2 and FP16RMulS1Of2
// Concise, end-to-end checks derived only from module ports, plus key coverage.

module FP16RMulS0Of2_sva(
  input logic        clk,
  input logic        rst,
  input logic [15:0] arg_0,
  input logic [15:0] arg_1,
  input logic        ret_0,
  input logic [4:0]  ret_1,
  input logic [4:0]  ret_2,
  input logic [11:0] ret_3
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Local recompute
  let s0  = arg_0[15];
  let s1  = arg_1[15];
  let e0  = arg_0[14:10];
  let e1  = arg_1[14:10];
  let f0  = arg_0[9:0];
  let f1  = arg_1[9:0];
  let ff0 = { (e0==5'd0)?1'b0:1'b1, f0 }; // 11b
  let ff1 = { (e1==5'd0)?1'b0:1'b1, f1 }; // 11b
  let p   = ff0 * ff1;                    // 22b
  let zz  = p[21:10];                     // 12b

  // Functional equivalence
  a_sign_xor:     assert property (ret_0 == (s0 ^ s1));
  a_exp_passthru: assert property (ret_1 == e0 && ret_2 == e1);
  a_prod_slice:   assert property (ret_3 == zz);

  // Sanity: zero-multiplicand => zero product slice
  a_zero_mult:    assert property ( (ff0==11'd0 || ff1==11'd0) |-> (ret_3==12'd0) );

  // No X on outputs when inputs are clean
  a_no_x:         assert property ( !$isunknown({arg_0,arg_1}) |-> !$isunknown({ret_0,ret_1,ret_2,ret_3}) );

  // Coverage
  c_norm_norm: cover property (e0!=0 && e1!=0 && f0!=0 && f1!=0);
  c_denorm_norm: cover property ((e0==0) ^ (e1==0));
  c_zero_any: cover property ((ff0==0) || (ff1==0));
  c_carry_out: cover property (p[21] == 1'b1); // normalization carry for next stage
  c_sign: cover property (ret_0==1'b0 ##1 ret_0==1'b1);
endmodule


module FP16RMulS1Of2_sva(
  input  logic        clk,
  input  logic        rst,
  input  logic        arg_0,       // s
  input  logic [4:0]  arg_1,       // e0
  input  logic [4:0]  arg_2,       // e1
  input  logic [11:0] arg_3,       // zz from stage0
  input  logic [15:0] ret_0
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Local recompute
  let s   = arg_0;
  let c   = arg_3[11];
  let fc  = c ? arg_3[10:1] : arg_3[9:0];       // normalized/shifted frac
  let infinput = (arg_1==5'd31) || (arg_2==5'd31);
  let e7  = ( {2'b00,arg_1} + {2'b00,arg_2} ) - 7'd15 + {6'b0,c}; // 7-bit unsigned
  let underflow = e7[6];
  let overflow  = (!underflow) && ( e7[5] || (e7[4:0]==5'd31) || infinput );
  let e   = underflow ? 5'd0 : (overflow ? 5'd31 : e7[4:0]);
  let uc  = (underflow || (e7[4:0]==5'd0)) ? 10'd0 : fc;
  let exp_frac_ok = {s,e,uc};

  // End-to-end check
  a_pack: assert property ( ret_0 == exp_frac_ok );

  // Key invariants
  a_ovf_implies_not_udf: assert property ( overflow |-> !underflow );
  a_zero_exp_zero_frac:  assert property ( (e==5'd0) |-> (uc==10'd0) );

  // No X on outputs when inputs are clean
  a_no_x: assert property ( !$isunknown({arg_0,arg_1,arg_2,arg_3}) |-> !$isunknown(ret_0) );

  // Coverage
  c_carry_paths:    cover property (c==1'b0 ##1 c==1'b1);
  c_underflow:      cover property (underflow);
  c_overflow:       cover property (overflow);
  c_normal:         cover property (!underflow && !overflow && (e!=0) && (e!=31));
  c_infinput:       cover property (infinput);
  c_uc_zero_nonzero: cover property (uc==10'd0 ##1 uc!=10'd0);
endmodule


// Bind to DUTs
bind FP16RMulS0Of2 FP16RMulS0Of2_sva b_s0 (
  .clk(clk), .rst(rst),
  .arg_0(arg_0), .arg_1(arg_1),
  .ret_0(ret_0), .ret_1(ret_1), .ret_2(ret_2), .ret_3(ret_3)
);

bind FP16RMulS1Of2 FP16RMulS1Of2_sva b_s1 (
  .clk(clk), .rst(rst),
  .arg_0(arg_0), .arg_1(arg_1), .arg_2(arg_2), .arg_3(arg_3),
  .ret_0(ret_0)
);
// SVA for controllerHdl_MATLAB_Function_block3_new
// Focus: functional equivalence, X-checks, stability, and corner-case coverage

module controllerHdl_MATLAB_Function_block3_new_sva #(parameter int W=19)
(
  input  logic                      CLK_IN,
  input  logic                      reset,
  input  logic                      enb_1_2000_0,
  input  logic signed [W-1:0]       u,
  input  logic signed [W-1:0]       y
);

  default clocking cb @(posedge CLK_IN); endclocking
  default disable iff (reset);

  // Reference model (matches RTL semantics, including logical right shifts)
  function automatic logic signed [W-1:0] u_n1_ref(input logic signed [W-1:0] a);
    return {1'b0, a[W-1:1]};
  endfunction

  function automatic logic signed [W-1:0] y_ref(input logic signed [W-1:0] a);
    return (a + u_n1_ref(a)) >> 1;
  endfunction

  // Signed-add overflow detector for coverage
  function automatic logic ovf_sadd(input logic signed [W-1:0] a,
                                    input logic signed [W-1:0] b,
                                    input logic signed [W-1:0] s);
    return (~(a[W-1]^b[W-1]) & (s[W-1]^a[W-1]));
  endfunction

  // A1: Functional equivalence to spec (whenever u is known)
  // If u is known, y must equal the combinational spec the same cycle.
  a_func: assert property ( !$isunknown(u) |-> (y == y_ref(u)) );

  // A2: Output must not be X/Z when enabled
  a_no_x_when_en: assert property ( enb_1_2000_0 |-> !$isunknown({u,y}) );

  // A3: Stability — if input is stable across cycles, output stays stable
  a_stable: assert property ( $stable(u) |-> $stable(y) );

  // A4: Enable independence — toggling enable does not affect y if u is unchanged
  a_enb_indep: assert property ( ($changed(enb_1_2000_0) && $stable(u)) |-> $stable(y) );

  // C1: Cover basic corner values
  c_zero:       cover property ( enb_1_2000_0 && (u == 19'sd0) );
  c_pos_one:    cover property ( enb_1_2000_0 && (u == 19'sd1) );
  c_neg_one:    cover property ( enb_1_2000_0 && (u == -19'sd1) );
  c_pos_max:    cover property ( enb_1_2000_0 && (u == 19'sd262143) );   // +2^18-1
  c_neg_min:    cover property ( enb_1_2000_0 && (u == -19'sd262144) );  // -2^18

  // C2: Cover addition overflow before final shift (u + u_n1)
  logic signed [W-1:0] sum_ref;
  always_comb sum_ref = u + u_n1_ref(u);
  c_add_overflow: cover property ( enb_1_2000_0 && ovf_sadd(u, u_n1_ref(u), sum_ref) );

  // C3: Cover sign change across consecutive cycles
  c_sign_flip: cover property ( enb_1_2000_0 && (u[W-1] != $past(u[W-1])) );

  // C4: Cover enable edges with stable input
  c_enb_edge: cover property ( ($rose(enb_1_2000_0) || $fell(enb_1_2000_0)) && $stable(u) );

  // C5: Cover reset release
  c_reset_rel: cover property ( $fell(reset) );

endmodule

// Bind into DUT
bind controllerHdl_MATLAB_Function_block3_new
  controllerHdl_MATLAB_Function_block3_new_sva #(.W(19))
  controllerHdl_MATLAB_Function_block3_new_sva_i (.*);
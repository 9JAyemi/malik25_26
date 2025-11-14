// SVA for cycloneii_mac_sign_ext
package cycloneii_mac_sign_ext_sva_pkg;

  module cycloneii_mac_sign_ext_sva (
    input  logic                 clk,
    input  logic signed [15:0]   data_in_a,
    input  logic signed [15:0]   data_in_b,
    input  logic                 enable,
    input  logic signed [31:0]   result
  );
    default clocking cb @(posedge clk); endclocking
    default disable iff ($isunknown({enable, data_in_a, data_in_b, result}));

    function automatic signed [31:0] trunc_mul_sext16(input signed [15:0] a, input signed [15:0] b);
      trunc_mul_sext16 = $signed((a*b)[15:0]); // low 16 bits, sign-extended to 32
    endfunction

    function automatic bit ovf32(input signed [31:0] x, input signed [31:0] y, input signed [31:0] z);
      ovf32 = (x[31] == y[31]) && (z[31] != x[31]);
    endfunction

    // Core behavior: enable-gated accumulate of sign-extended low-16-bit product
    a_en_update: assert property (enable |=> result == $past(result) +
                                            trunc_mul_sext16($past(data_in_a), $past(data_in_b)));

    // Hold when disabled
    a_dis_hold:  assert property (!enable |=> result == $past(result));

    // Basic functional coverage
    c_pp: cover property (enable && !data_in_a[15] && !data_in_b[15]);
    c_pn: cover property (enable && !data_in_a[15] &&  data_in_b[15]);
    c_np: cover property (enable &&  data_in_a[15] && !data_in_b[15]);
    c_nn: cover property (enable &&  data_in_a[15] &&  data_in_b[15]);

    // Truncation actually changes the product vs full 32-bit product
    c_truncation_effect: cover property (enable |=> $signed($past(data_in_a) * $past(data_in_b)) !=
                                                   trunc_mul_sext16($past(data_in_a), $past(data_in_b)));

    // Accumulator signed overflow coverage
    c_accum_overflow: cover property (enable |=> ovf32($past(result),
                                                       trunc_mul_sext16($past(data_in_a), $past(data_in_b)),
                                                       result));

    // Explicit hold coverage
    c_hold: cover property (!enable |=> result == $past(result));
  endmodule

endpackage

// Bind into the DUT (connects by name)
bind cycloneii_mac_sign_ext cycloneii_mac_sign_ext_sva_pkg::cycloneii_mac_sign_ext_sva b_cycloneii_mac_sign_ext_sva (.*);
// SVA package + binders for bitwise_or_multiplier/top_module
package bitwise_or_multiplier_sva_pkg;

  // Checker bound into bitwise_or_multiplier; sees internal or_result
  module bitwise_or_multiplier_sva #(parameter int C = 42) (
    input logic [7:0]  byte1,
    input logic [7:0]  byte2,
    input logic [7:0]  or_result,
    input logic [15:0] result
  );
    // Sample on any relevant combinational change
    default clocking cb @ (byte1 or byte2 or or_result or result); endclocking

    // Parameter sanity (elaboration-time)
    initial assert (C == 42) else $error("constant_value != 42");

    // Core correctness
    ap_no_x:     assert property ( !$isunknown({byte1,byte2}) |-> (!$isunknown(or_result) && !$isunknown(result)) );
    ap_or:       assert property ( or_result == (byte1 | byte2) );
    ap_mul:      assert property ( result == (or_result * C) );
    ap_end2end:  assert property ( result == ((byte1 | byte2) * C) );

    // Functional coverage
    cp_zero:          cover property ( byte1==8'h00 && byte2==8'h00 && or_result==8'h00 && result==16'd0 );
    cp_all_ones:      cover property ( byte1==8'hFF && byte2==8'hFF && or_result==8'hFF && result==16'd10710 );
    cp_disjoint:      cover property ( byte1==8'hAA && byte2==8'h55 && or_result==8'hFF );
    cp_overlap:       cover property ( byte1==8'hF0 && byte2==8'hF0 && or_result==8'hF0 );
    cp_upper_nonzero: cover property ( result[15:8] != 8'h00 );

    genvar i;
    for (i=0; i<8; i++) begin : g_onehot_cov
      cp_onebit: cover property ( or_result == (8'h1 << i) );
    end
  endmodule

  // End-to-end checker bound into top_module
  module top_module_sva;
    // Implicit ports via bind connection
    default clocking cb @ (*); endclocking
    ap_top_e2e: assert property ( result == ((byte1 | byte2) * 16'd42) );
    cp_top_max: cover property ( result == 16'd10710 );
  endmodule

endpackage

// Binds
bind bitwise_or_multiplier bitwise_or_multiplier_sva_pkg::bitwise_or_multiplier_sva #(.C(constant_value))
  u_bom_sva (.byte1(byte1), .byte2(byte2), .or_result(or_result), .result(result));

bind top_module bitwise_or_multiplier_sva_pkg::top_module_sva u_top_sva (.byte1(byte1), .byte2(byte2), .result(result));
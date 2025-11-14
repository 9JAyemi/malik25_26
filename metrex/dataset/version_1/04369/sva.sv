// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic [2:0]  sel,
  input logic [3:0]  data0, data1, data2, data3, data4, data5,
  input logic [3:0]  out_mux,
  input logic [2:0]  out_3bit,
  input logic        o2, o1, o0,
  input logic [6:0]  final_out
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [4:0] sum5(input logic [3:0] m, input logic [2:0] s);
    sum5 = {1'b0, m} + {2'b0, s};
  endfunction

  // No-X propagation: if inputs known, outputs known
  ap_known: assert property (
    !$isunknown({sel, data0, data1, data2, data3, data4, data5})
    |-> !$isunknown({out_mux, out_3bit, o2, o1, o0, final_out})
  );

  // 6:1 MUX behavior (incl. default)
  ap_mux: assert property (
    out_mux ==
      ((sel==3'd0) ? data0 :
       (sel==3'd1) ? data1 :
       (sel==3'd2) ? data2 :
       (sel==3'd3) ? data3 :
       (sel==3'd4) ? data4 :
       (sel==3'd5) ? data5 : 4'b0)
  );

  // 3-bit pass-through and bit-slices
  ap_sel_bits: assert property (
    (out_3bit == sel) && (o2 == sel[2]) && (o1 == sel[1]) && (o0 == sel[0])
  );

  // Functional module result (note: final_out is zero-extended 5-bit sum)
  ap_final: assert property (
    final_out == {2'b00, sum5(out_mux, sel)}
  );

  // Coverage: all select values, default path, and sum extremes
  genvar i;
  generate for (i=0; i<8; i++) begin : g_sel_cov
    cp_sel: cover property (sel == i[2:0]);
  end endgenerate
  cp_default: cover property ((sel > 3'd5) && (out_mux == 4'b0));
  cp_sum_zero: cover property (sum5(out_mux, sel) == 5'd0);
  cp_sum_max:  cover property (sum5(out_mux, sel) == 5'd31);

  // Coverage that each selected input appears at the output
  cp_mux0: cover property ((sel==3'd0) && (out_mux==data0));
  cp_mux1: cover property ((sel==3'd1) && (out_mux==data1));
  cp_mux2: cover property ((sel==3'd2) && (out_mux==data2));
  cp_mux3: cover property ((sel==3'd3) && (out_mux==data3));
  cp_mux4: cover property ((sel==3'd4) && (out_mux==data4));
  cp_mux5: cover property ((sel==3'd5) && (out_mux==data5));

endmodule

bind top_module top_module_sva sva_i (.*);
// Concise SVA binders for byte_reverse and top_module.
// Uses $global_clock for combinational checking.

bind byte_reverse byte_reverse_sva u_byte_reverse_sva(.in(in), .out(out));
module byte_reverse_sva(input logic [31:0] in, input logic [31:0] out);
  default clocking cb @($global_clock); endclocking

  // Functional correctness
  a_rev_eq:  assert property (out == {in[7:0], in[15:8], in[23:16], in[31:24]});

  // X-prop
  a_rev_known: assert property (!$isunknown(in) |-> !$isunknown(out));

  // Minimal functional coverage
  c_rev_byte: cover property (out[7:0] == in[31:24]);
endmodule


bind top_module top_module_sva u_top_module_sva(
  .in(in), .sel(sel),
  .data0(data0), .data1(data1), .data2(data2),
  .data3(data3), .data4(data4), .data5(data5),
  .out(out),
  .reversed_in(reversed_in),
  .and_output(and_output),
  .mux_output(mux_output),
  .add_output(add_output)
);
module top_module_sva(
  input logic [31:0] in,
  input logic [2:0]  sel,
  input logic [7:0]  data0, data1, data2, data3, data4, data5,
  input logic [7:0]  out,
  input logic [31:0] reversed_in,
  input logic [7:0]  and_output, mux_output, add_output
);
  default clocking cb @($global_clock); endclocking

  // AND output is 2-bit result zero-extended to 8
  a_and_hi_zero: assert property (and_output[7:2] == '0);
  a_and_val:     assert property (and_output[1:0] ==
                                  (data0[1:0] & data1[1:0] & data2[1:0] &
                                   data3[1:0] & data4[1:0] & data5[1:0]));

  // Mux select mapping
  a_mux_0:  assert property ((sel==3'd0) |-> mux_output == data0);
  a_mux_1:  assert property ((sel==3'd1) |-> mux_output == data1);
  a_mux_2:  assert property ((sel==3'd2) |-> mux_output == data2);
  a_mux_3:  assert property ((sel==3'd3) |-> mux_output == data3);
  a_mux_4:  assert property ((sel==3'd4) |-> mux_output == data4);
  a_mux_5:  assert property ((sel==3'd5) |-> mux_output == data5);
  a_mux_67: assert property ((sel inside {3'd6,3'd7}) |-> mux_output == and_output);

  // Addition and final output
  a_add_eq: assert property (add_output == (reversed_in[7:0] + mux_output));
  a_out_eq: assert property (out == add_output);

  // Overall spec equivalence (redundant but tight)
  a_spec_eq: assert property (out == (in[31:24] + mux_output));

  // X-prop: known inputs imply known internal nets/outputs
  a_known: assert property (
    !$isunknown({in, sel, data0, data1, data2, data3, data4, data5})
    |->
    !$isunknown({reversed_in, and_output, mux_output, add_output, out})
  );

  // Minimal coverage
  c_sel0: cover property (sel==3'd0);
  c_sel1: cover property (sel==3'd1);
  c_sel2: cover property (sel==3'd2);
  c_sel3: cover property (sel==3'd3);
  c_sel4: cover property (sel==3'd4);
  c_sel5: cover property (sel==3'd5);
  c_sel6: cover property (sel==3'd6);
  c_sel7: cover property (sel==3'd7);

  c_and_zero:    cover property (and_output[1:0] == 2'b00);
  c_and_allones: cover property (and_output[1:0] == 2'b11);

  // Addition overflow (carry-out dropped)
  c_add_overflow: cover property (out < in[31:24]);
endmodule
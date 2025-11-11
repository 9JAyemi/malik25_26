// SVA for splitter
module splitter_sva (
  input logic [2:0] in,
  input logic       o2, o1, o0
);
  // Functional equivalence
  a_splitter_map: assert property (@(in or o2 or o1 or o0) {o2,o1,o0} == in);

  // Simple functional coverage of all 3-bit patterns
  genvar k;
  generate
    for (k=0; k<8; k++) begin: g_cov
      c_splitter_vals: cover property (@(in or o2 or o1 or o0)
        (in == k[2:0]) && ({o2,o1,o0} == k[2:0]));
    end
  endgenerate
endmodule

bind splitter splitter_sva u_splitter_sva(.in(in), .o2(o2), .o1(o1), .o0(o0));



// SVA for barrel_shifter
module barrel_shifter_sva (
  input  logic [15:0] in,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo
);
  // Exact mapping of shift and split
  a_barrel_concat: assert property (@(in or out_hi or out_lo)
    {out_hi, out_lo} == (in >> 8));

  // Redundant but explicit checks
  a_barrel_hi_zero: assert property (@(in or out_hi) out_hi == 8'h00);
  a_barrel_lo_map:  assert property (@(in or out_lo) out_lo == in[15:8]);

  // Basic coverage of zero/nonzero shifted window
  c_barrel_zero:    cover property (@(in) in[15:8] == 8'h00);
  c_barrel_nonzero: cover property (@(in) in[15:8] != 8'h00);
endmodule

bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva(.in(in), .out_hi(out_hi), .out_lo(out_lo));



// SVA for top_module
module top_module_sva (
  input  logic [18:0] in,
  input  logic        select,
  input  logic [18:0] out,
  input  logic        o2, o1, o0,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo
);
  // Assume clean inputs to avoid X/Z-driven false failures
  assume_clean_inputs: assume property (@(in or select) !$isunknown({in,select}));

  // Splitter passthrough at top ports
  a_top_splitter: assert property (@(in or o2 or o1 or o0) {o2,o1,o0} == in[2:0]);

  // Barrel outputs as seen at top ports
  a_top_out_hi_zero: assert property (@(out_hi or in) out_hi == 8'h00);
  a_top_out_lo_map:  assert property (@(out_lo or in) out_lo == in[18:11]);

  // Structural consistency between out and sub-outputs
  a_out_upper_matches_hi: assert property (@(out or out_hi) out[18:11] == out_hi);
  a_out_lower_matches_lo: assert property (@(out or out_lo) out[7:0]   == out_lo);
  a_out_midbits:          assert property (@(out or select or in or o2 or o1 or o0)
                               out[10:8] == (select ? in[2:0] : 3'b000));

  // Full end-to-end mapping for both select cases
  a_out_sel0: assert property (@(out or select or in)
                    !select |-> out == {3'b000, 8'h00, in[18:11]});
  a_out_sel1: assert property (@(out or select or in or o2 or o1 or o0)
                     select |-> out == {8'h00, in[2:0], in[18:11]});

  // No X/Z on outputs under clean inputs
  a_no_x_on_outputs: assert property (@(out or o2 or o1 or o0 or out_hi or out_lo)
                          !$isunknown({out, o2, o1, o0, out_hi, out_lo}));

  // Coverage: exercise both mux paths and insertion of nonzero splitter bits
  c_sel0_seen: cover property (@(select) !select);
  c_sel1_seen: cover property (@(select)  select);
  c_insert_nonzero: cover property (@(select or in) select && (in[2:0] != 3'b000));
endmodule

bind top_module top_module_sva u_top_module_sva(
  .in(in), .select(select), .out(out),
  .o2(o2), .o1(o1), .o0(o0), .out_hi(out_hi), .out_lo(out_lo)
);
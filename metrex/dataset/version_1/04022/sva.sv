// SystemVerilog Assertions (SVA) for the provided design
// Bind-ready, concise, and focused on functional correctness and coverage

// Decoder checker
module decoder_sva(input logic [3:0] in, input logic [15:0] out);
  // Functional correctness
  assert property (@(in or out) !$isunknown(in) |-> (out == (16'h0001 << in)));
  assert property (@(in or out) !$isunknown(in) |-> $onehot(out));

  // Full input coverage (all 16 values)
  genvar i;
  for (i=0; i<16; i++) begin : g_dec_cov
    cover property (@(in) (in === i[3:0]));
  end
endmodule


// 4:1 mux checker
module mux_4to1_sva(
  input logic [3:0] in0, in1, in2, in3,
  input logic [1:0] select,
  input logic [3:0] out
);
  // Functional correctness for known inputs/select
  assert property (@(in0 or in1 or in2 or in3 or select)
                   !$isunknown({select,in0,in1,in2,in3})
                   |-> (out == (select[1] ? (select[0] ? in3 : in2)
                                           : (select[0] ? in1 : in0))));
  // Select coverage
  genvar s;
  for (s=0; s<4; s++) begin : g_mux_sel_cov
    cover property (@(select) (select === s[1:0]));
  end
endmodule


// Top-level composition checker
module top_module_sva(
  input  logic [3:0]  in,
  input  logic [15:0] out,
  // Internal nets to strengthen cross-module checks
  input  logic [15:0] decoder_out,
  input  logic [3:0]  mux_out
);
  // Structural: out is zero-extended mux_out
  assert property (@(out or mux_out) (out === {12'b0, mux_out}));

  // Functional: out == zero-extend(1 << in[1:0]) when inputs known
  assert property (@(in or out) !$isunknown(in)
                   |-> (out[15:4] == 12'h000 && out[3:0] == (4'h1 << in[1:0])));

  // Cross-check: selected nibble from decoder matches mux_out and out
  assert property (@(in or decoder_out or mux_out or out)
                   !$isunknown(in)
                   |-> (((decoder_out >> {in[3:2],2'b00})[3:0]) == mux_out
                        && out[3:0] == mux_out));

  // Decoder nibble one-hot at the position in[1:0]
  assert property (@(in or decoder_out)
                   !$isunknown(in) |-> (((decoder_out >> {in[3:2],2'b00})[3:0]) == (4'h1 << in[1:0])));

  // Full 16-value input coverage at top
  genvar k;
  for (k=0; k<16; k++) begin : g_top_cov
    cover property (@(in) (in === k[3:0]));
  end
endmodule


// Bind statements
bind decoder    decoder_sva    u_decoder_sva   (.in(in), .out(out));
bind mux_4to1   mux_4to1_sva   u_mux_4to1_sva  (.in0(in0), .in1(in1), .in2(in2), .in3(in3), .select(select), .out(out));
bind top_module top_module_sva u_top_module_sva(.in(in), .out(out), .decoder_out(decoder_out), .mux_out(mux_out));
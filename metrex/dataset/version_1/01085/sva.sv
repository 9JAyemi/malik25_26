// SVA for byte_reversal and priority_encoder
// Bind these into the DUTs and connect a sampling clock 'clk'.

// ----------------- byte_reversal SVA -----------------
module byte_reversal_sva(
  input logic clk,
  input logic [31:0] in,
  input logic [31:0] out
);
  default clocking @(posedge clk); endclocking

  // Functional equivalence (full byte swap)
  a_swap_eq: assert property (out == {in[7:0], in[15:8], in[23:16], in[31:24]});

  // Known in => known out
  a_no_x: assert property (!$isunknown(in)) |-> (!$isunknown(out));

  // Per-byte dependency (only the mapped output byte changes when only one input byte changes)
  a_dep_b3: assert property ($changed(in[31:24]) && !$changed(in[23:0])
                             |-> $changed(out[7:0]) && !$changed(out[31:8]));
  a_dep_b2: assert property ($changed(in[23:16]) && !$changed(in[31:24]) && !$changed(in[15:0])
                             |-> $changed(out[15:8]) && !$changed(out[31:16]) && !$changed(out[7:0]));
  a_dep_b1: assert property ($changed(in[15:8])  && !$changed(in[31:24]) && !$changed(in[23:16]) && !$changed(in[7:0])
                             |-> $changed(out[23:16]) && !$changed(out[31:24]) && !$changed(out[15:0]));
  a_dep_b0: assert property ($changed(in[7:0])   && !$changed(in[31:8])
                             |-> $changed(out[31:24]) && !$changed(out[23:0]));

  // Coverage: observe each byte mapping at least once
  c_b3: cover property ($changed(in[31:24]) ##1 (out[7:0]  == $past(in[31:24])));
  c_b2: cover property ($changed(in[23:16]) ##1 (out[15:8] == $past(in[23:16])));
  c_b1: cover property ($changed(in[15:8])  ##1 (out[23:16]== $past(in[15:8])));
  c_b0: cover property ($changed(in[7:0])   ##1 (out[31:24]== $past(in[7:0])));
endmodule

bind byte_reversal byte_reversal_sva u_byte_reversal_sva(.clk(clk), .in(in), .out(out));

// ----------------- priority_encoder SVA -----------------
module priority_encoder_sva(
  input logic clk,
  input logic [31:0] in,
  input logic [4:0]  pos
);
  default clocking @(posedge clk); endclocking

  // Helper: 32-bit run of 1s from LSB, i.e., in == (2^k - 1)
  function automatic bit run_of_ones32 (logic [31:0] x);
    return ((x & (x + 32'd1)) == 32'd0);
  endfunction

  // Legal output space per RTL: 0..11 or 15
  a_pos_legal: assert property (pos <= 5'd11 || pos == 5'd15);

  // For runs of ones with k in [0..11], pos must equal k
  a_map_run_k: assert property (run_of_ones32(in) && ($countones(in) <= 12'd11)
                                |-> pos == $countones(in));

  // For everything else (non-run patterns or k >= 12), pos must be 15 (default)
  a_default_else: assert property (( !run_of_ones32(in) ) || ($countones(in) > 12'd11)
                                   |-> pos == 5'd15);

  // Known in => known pos
  a_no_x: assert property (!$isunknown(in)) |-> (!$isunknown(pos));

  // Coverage: hit each enumerated k and default paths
  genvar k;
  generate
    for (k = 0; k <= 11; k++) begin : gen_cov_k
      c_k: cover property (run_of_ones32(in) && ($countones(in) == k) && (pos == k));
    end
  endgenerate
  c_default_nonrun: cover property (!run_of_ones32(in) && pos == 5'd15);
  c_default_bigk:   cover property (run_of_ones32(in) && ($countones(in) > 11) && pos == 5'd15);
endmodule

bind priority_encoder priority_encoder_sva u_priority_encoder_sva(.clk(clk), .in(in), .pos(pos));
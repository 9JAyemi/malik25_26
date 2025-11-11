// SVA for decoder_bcd system. Focused, high-quality checks and coverage.

package decoder_bcd_sva_pkg;

  function automatic int oh_index16(input logic [15:0] v);
    int j;
    oh_index16 = -1;
    for (j=0; j<16; j++) if (v[j]) oh_index16 = j;
  endfunction

  function automatic logic [3:0] map_idx_to_bcd(input int idx);
    logic [3:0] r;
    if (idx < 0) r = 4'h0;
    else r = ((idx % 9) + 1);
    return r;
  endfunction

  function automatic logic [3:0] map_bin_to_bcd(input logic [3:0] bin);
    int n;
    n = bin;
    return ((n % 9) + 1);
  endfunction

endpackage

import decoder_bcd_sva_pkg::*;


// Decoder: exact one-hot shift and full input coverage
module sva_decoder_4to16(input logic [3:0] in, input logic [15:0] out);
  assert property (@(in) !$isunknown(in) |-> ##0 out == (16'h1 << in));
  assert property (@(in) !$isunknown(in) |-> ##0 $onehot(out));
  genvar i;
  for (i=0; i<16; i++) begin
    cover property (@(in) in == i[3:0]);
    cover property (@(out) out == (16'h1 << i));
  end
endmodule


// BCD encoder: correct mapping for one-hot; default on invalid inputs; full coverage
module sva_bcd_encoder(input logic [15:0] in, input logic [3:0] out);
  assert property (@(in) $onehot(in) |-> ##0 out == map_idx_to_bcd(oh_index16(in)));
  assert property (@(in) !$isunknown(in) && !$onehot(in) |-> ##0 out == 4'h0);
  genvar k;
  for (k=0; k<16; k++) begin
    cover property (@(in) in == (16'h1 << k) && ##0 out == map_idx_to_bcd(k));
  end
endmodule


// Chain-level checks inside decoder_bcd: decode correctness, encoder correctness, wiring, and E2E
module sva_decoder_bcd(
  input logic [3:0] binary_in,
  input logic [3:0] out_high,
  input logic [3:0] out_low,
  input logic [15:0] decoder_out,
  input logic [3:0] bcd_out
);
  assert property (@(binary_in) !$isunknown(binary_in) |-> ##0 decoder_out == (16'h1 << binary_in));
  assert property (@(decoder_out) $onehot(decoder_out));
  assert property (@(binary_in) !$isunknown(binary_in) |-> ##0 bcd_out == map_bin_to_bcd(binary_in));

  // Output wiring (both outputs mirror bcd_out in RTL)
  assert property (@(bcd_out or out_high or out_low) ##0 (out_high == bcd_out && out_low == bcd_out));
  assert property (@(out_high or out_low) out_high == out_low);

  // End-to-end expected behavior from binary_in
  assert property (@(binary_in) !$isunknown(binary_in) |-> ##0
                   (out_high == map_bin_to_bcd(binary_in) && out_low == map_bin_to_bcd(binary_in)));

  // Full path coverage
  genvar m;
  for (m=0; m<16; m++) begin
    cover property (@(binary_in)
      binary_in == m[3:0] ##0
      decoder_out == (16'h1 << m) ##0
      bcd_out == map_bin_to_bcd(m[3:0]) ##0
      (out_high == bcd_out && out_low == bcd_out)
    );
  end
endmodule


// Top-level connectivity/end-to-end check and input coverage
module sva_top_module(
  input logic A, B, C, D,
  input logic [3:0] out_high,
  input logic [3:0] out_low
);
  wire [3:0] bin = {A,B,C,D};
  assert property (@(A or B or C or D) !$isunknown(bin) |-> ##0
                   (out_high == map_bin_to_bcd(bin) && out_low == map_bin_to_bcd(bin)));
  genvar t;
  for (t=0; t<16; t++) begin
    cover property (@(A or B or C or D) bin == t[3:0]);
  end
endmodule


// Bind assertions
bind decoder_4to16 sva_decoder_4to16 u_sva_decoder_4to16 (.*);
bind bcd_encoder  sva_bcd_encoder  u_sva_bcd_encoder  (.*);
bind decoder_bcd  sva_decoder_bcd  u_sva_decoder_bcd  (.*);
bind top_module   sva_top_module   u_sva_top_module   (.*);
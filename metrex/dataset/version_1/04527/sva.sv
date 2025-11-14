// SVA checkers and binds for top_module design
// Purely combinational: use immediate assertions in always_comb and immediate cover

// byte_decoder checker
module byte_decoder_sva (
  input logic [15:0] in,
  input logic [7:0]  out_hi,
  input logic [7:0]  out_lo
);
  always_comb begin
    assert (out_hi === in[15:8]) else $error("byte_decoder: out_hi != in[15:8]");
    assert (out_lo === in[7:0])  else $error("byte_decoder: out_lo != in[7:0]");

    // Sanity coverage
    cover (in == 16'h0000);
    cover (in == 16'hFFFF);
  end
endmodule

// byte_mux checker
module byte_mux_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic       sel,
  input logic [7:0] out
);
  always_comb begin
    assert (out === (sel ? b : a)) else $error("byte_mux: out != (sel ? b : a)");

    // Select coverage
    cover (sel == 1'b0);
    cover (sel == 1'b1);
  end
endmodule

// top_module checker
module top_module_sva (
  input logic [15:0] in,
  input logic [7:0]  out_hi,
  input logic [7:0]  out_lo,
  input logic [7:0]  sum_hi,
  input logic [7:0]  sum_lo
);
  always_comb begin
    // Decoder outputs
    assert (sum_hi === in[15:8]) else $error("top: sum_hi != in[15:8]");
    assert (sum_lo === in[7:0])  else $error("top: sum_lo != in[7:0]");

    // Muxed outputs vs internal wires
    assert (out_hi === (in[15] ? 8'h00 : sum_hi)) else $error("top: out_hi mux mismatch");
    assert (out_lo === (in[7]  ? 8'h00 : sum_lo)) else $error("top: out_lo mux mismatch");

    // Direct spec (end-to-end)
    assert (out_hi === (in[15] ? 8'h00 : in[15:8])) else $error("top: out_hi != spec");
    assert (out_lo === (in[7]  ? 8'h00 : in[7:0]))  else $error("top: out_lo != spec");

    // Assert outputs are known
    assert (!$isunknown(out_hi)) else $error("top: out_hi has X/Z");
    assert (!$isunknown(out_lo)) else $error("top: out_lo has X/Z");

    // Functional coverage: all select combinations and a couple of mixed-data patterns
    cover (!in[15] && !in[7]);
    cover ( in[15] && !in[7]);
    cover (!in[15] &&  in[7]);
    cover ( in[15] &&  in[7]);
    cover (in[15:8] == 8'hAA && in[7:0] == 8'h55);
    cover (in[15:8] == 8'h55 && in[7:0] == 8'hAA);
  end
endmodule

// Binds
bind byte_decoder byte_decoder_sva u_byte_decoder_sva (
  .in(in), .out_hi(out_hi), .out_lo(out_lo)
);

bind byte_mux byte_mux_sva u_byte_mux_sva (
  .a(a), .b(b), .sel(sel), .out(out)
);

bind top_module top_module_sva u_top_module_sva (
  .in(in), .out_hi(out_hi), .out_lo(out_lo), .sum_hi(sum_hi), .sum_lo(sum_lo)
);
// SVA for manchester_encoder and manchester_decoder
// Focus: concise, high-quality checks and coverage. Bind into DUTs as-is.

package manchester_sva_pkg;

  // Encoder SVA
  module manchester_encoder_sva #(
    parameter int n = 4,
    parameter int m = 2
  ) (
    input logic               clk,
    input logic [n-1:0]       in,
    input logic [m-1:0]       out
  );
    // Static sanity: encoder hard-codes 2-bit symbols
    initial if (m != 2) $error("manchester_encoder: m must be 2 (got %0d)", m);

    default clocking cb @(posedge clk); endclocking

    // Functional mapping (when inputs are known): change -> 2'b10, no-change -> 2'b01
    a_enc_func: assert property (
      (!$isunknown(in) && !$isunknown($past(in))) |-> ((in == $past(in)) ? (out == 2'b01) : (out == 2'b10))
    );

    // Out is always exactly one-hot and complementary
    a_enc_onehot:        assert property ( !$isunknown(out) |-> $onehot(out) );
    a_enc_complementary: assert property ( !$isunknown(out) |-> (out[1] === ~out[0]) );

    // Coverage: no-change, single-bit change, multi-bit change
    c_enc_nochange:         cover property ( (!$isunknown(in) && !$isunknown($past(in))) && (in == $past(in)) && (out == 2'b01) );
    c_enc_singlebit_change: cover property ( (!$isunknown(in) && !$isunknown($past(in))) && ($countones(in ^ $past(in)) == 1) && (out == 2'b10) );
    c_enc_multibit_change:  cover property ( (!$isunknown(in) && !$isunknown($past(in))) && ($countones(in ^ $past(in)) >= 2) && (out == 2'b10) );
  endmodule

  // Decoder SVA
  module manchester_decoder_sva #(
    parameter int n = 4,
    parameter int m = 2
  ) (
    input logic               clk,
    input logic [n-1:0]       in,
    input logic [m-1:0]       out
  );
    default clocking cb @(posedge clk); endclocking

    // Only LSB is used; upper bits must be 0 (handles m>=1)
    if (m > 1) begin : g_upper_zero
      a_dec_upper_zero: assert property ( out[m-1:1] == '0 );
    end

    // Functional mapping (when inputs are known): change -> 1 in LSB, no-change -> all 0s
    a_dec_func: assert property (
      (!$isunknown(in) && !$isunknown($past(in))) |->
        ((in == $past(in)) ? (out == '0) : (out == {{m-1{1'b0}},1'b1}))
    );

    // No false positives: LSB=1 implies there was a change
    a_dec_imp: assert property ( out[0] == 1'b1 |-> (in != $past(in)) );

    // Coverage: no-change, single-bit change, multi-bit change
    c_dec_nochange:         cover property ( (!$isunknown(in) && !$isunknown($past(in))) && (in == $past(in)) && (out == '0) );
    c_dec_singlebit_change: cover property ( (!$isunknown(in) && !$isunknown($past(in))) && ($countones(in ^ $past(in)) == 1) && (out == {{m-1{1'b0}},1'b1}) );
    c_dec_multibit_change:  cover property ( (!$isunknown(in) && !$isunknown($past(in))) && ($countones(in ^ $past(in)) >= 2) && (out == {{m-1{1'b0}},1'b1}) );
  endmodule

endpackage

// Bind into DUTs
import manchester_sva_pkg::*;

bind manchester_encoder manchester_encoder_sva #(.n(n), .m(m)) enc_sva_i (.clk(clk), .in(in), .out(out));
bind manchester_decoder manchester_decoder_sva #(.n(n), .m(m)) dec_sva_i (.clk(clk), .in(in), .out(out));
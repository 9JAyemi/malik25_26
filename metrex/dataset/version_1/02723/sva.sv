// SVA bind module for decoder
module decoder_sva;
  // Bind into DUT, access internals
  bind decoder decoder_sva_i (.*);
endmodule

module decoder_sva_i (
  input  logic        sel2, sel1, sel0, clk,
  input  logic [63:0] out,
  input  logic [63:0] stage1_out,
  input  logic [63:0] stage2_out
);

  // reference decode (intended behavior)
  function automatic logic [63:0] decode_ref (input logic s2, s1, s0);
    logic [63:0] r = '0;
    unique case ({s2,s1,s0})
      3'b000: r[0]  = 1'b1;
      3'b100: r[8]  = 1'b1;
      3'b011: r[56] = 1'b1; // note: 011 duplicated in DUT; later branch unreachable
      3'b110: r[60] = 1'b1;
      default: r     = '0;
    endcase
    return r;
  endfunction

  // past-valid guard
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // No X/Z on outputs and internal pipeline
  assert property (cb !$isunknown(out)) else $error("out has X/Z");
  assert property (cb !$isunknown(stage2_out)) else $error("stage2_out has X/Z");
  assert property (cb !$isunknown(stage1_out)) else $error("stage1_out has X/Z (possible latch/partial assignment)");

  // One-hot-or-zero on stage1_out and out
  assert property (cb $onehot0(stage1_out)) else $error("stage1_out not onehot0");
  assert property (cb $onehot0(out))        else $error("out not onehot0");

  // Pipeline transfer correctness
  assert property (cb disable iff (!past_valid) stage2_out == $past(stage1_out))
    else $error("stage2_out != past stage1_out");
  assert property (cb out == stage2_out)
    else $error("out != stage2_out");

  // Functional behavior: 1-cycle latency vs decode_ref
  assert property (cb disable iff (!past_valid) out == $past(decode_ref(sel2,sel1,sel0)))
    else $error("out != expected decode_ref with 1-cycle latency");

  // Specific mapping checks (redundant with decode_ref but give targeted messages)
  assert property (cb disable iff (!past_valid) $past({sel2,sel1,sel0})==3'b000 |-> out[0]  && (out==64'h1<<0))
    else $error("000 -> bit0 decode failed");
  assert property (cb disable iff (!past_valid) $past({sel2,sel1,sel0})==3'b100 |-> out[8]  && (out==64'h1<<8))
    else $error("100 -> bit8 decode failed");
  assert property (cb disable iff (!past_valid) $past({sel2,sel1,sel0})==3'b011 |-> out[56] && (out==64'h1<<56))
    else $error("011 -> bit56 decode failed");
  assert property (cb disable iff (!past_valid) $past({sel2,sel1,sel0})==3'b110 |-> out[60] && (out==64'h1<<60))
    else $error("110 -> bit60 decode failed");
  assert property (cb disable iff (!past_valid) !($past({sel2,sel1,sel0}) inside {3'b000,3'b100,3'b011,3'b110}) |-> out=='0)
    else $error("Unexpected nonzero decode for unmapped select");

  // Coverage: hit each mapped case and the default; also flag unreachable 48 if ever produced
  cover property (cb $past({sel2,sel1,sel0})==3'b000 && out[0]);
  cover property (cb $past({sel2,sel1,sel0})==3'b100 && out[8]);
  cover property (cb $past({sel2,sel1,sel0})==3'b011 && out[56]);
  cover property (cb $past({sel2,sel1,sel0})==3'b110 && out[60]);
  cover property (cb !($past({sel2,sel1,sel0}) inside {3'b000,3'b100,3'b011,3'b110}) && out=='0);
  // Unreachable-intent detector (due to duplicated 3'b011 in DUT)
  cover property (cb out[48]);

endmodule
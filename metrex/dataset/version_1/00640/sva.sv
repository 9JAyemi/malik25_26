// Drop-in SVA for FpuFp32. Bind or place inside the FpuFp32 module.
// Focus: mux correctness, internal wiring, pipeline/latency checks, X checks, and concise coverage.

`ifndef FPU_FP32_SVA
`define FPU_FP32_SVA

// synopsys translate_off
// pragma translate_off
`ifdef SVA

// Place this block inside module FpuFp32 or bind it:
// bind FpuFp32 FpuFp32_sva u_FpuFp32_sva();

default clocking cb @(posedge clk); endclocking

logic past_valid;
initial past_valid = 1'b0;
always @(posedge clk) past_valid <= 1'b1;

// ---------- Structural wiring checks ----------
assert property (cb (fpaIsSub == (opMode == OP_SUB)))
  else $error("fpaIsSub must follow opMode==SUB");

assert property (cb (fpmSrcB == ((opMode == OP_DIV) ? fpRcpDst : srcb)))
  else $error("fpmSrcB DIV select mismatch");

// ---------- Mux/output decode checks (same-cycle) ----------
localparam [31:0] ONE_F = 32'h3F80_0000;

assert property (cb (opMode == OP_ADD) |-> (dst == fpaDst));
assert property (cb (opMode == OP_SUB) |-> (dst == fpaDst));
assert property (cb (opMode == OP_MUL) |-> (dst == fpmDst));
assert property (cb (opMode == OP_DIV) |-> (dst == fpmDst));
assert property (cb (opMode == OP_RCP) |-> (dst == fpRcpDst));
assert property (cb (opMode == OP_ABS) |-> (dst == (srcb[31] ? -srcb : srcb)));
assert property (cb (opMode == OP_NEG) |-> (dst == -srcb));
assert property (cb (opMode == OP_SQRT) |-> (dst == (((srcb - ONE_F) >>> 1) + ONE_F)));

// If opMode is not a known opcode, dst must pass-through srcb
assert property (cb (!(opMode inside {OP_NONE,OP_ADD,OP_SUB,OP_MUL,OP_DIV,OP_ABS,OP_NEG,OP_RCP,OP_SQRT})) |->
                      (dst == srcb));

// ---------- Submodule latency/cycle-accurate checks ----------
/* Adder: 1-cycle registered result of sum/diff using fpaIsSub at the sampling edge */
assert property (cb past_valid |-> (fpaDst == $past(fpaIsSub ? (srca - srcb) : (srca + srcb))))
  else $error("Adder latency/result mismatch");

/* Multiplier: 1-cycle registered result of srca * fpmSrcB */
assert property (cb past_valid |-> (fpmDst == $past(srca * fpmSrcB)))
  else $error("Multiplier latency/result mismatch");

/* Reciprocal: 1-cycle registered result of ONE_F / srcb */
assert property (cb past_valid |-> (fpRcpDst == $past(ONE_F / srcb)))
  else $error("RCP latency/result mismatch");

// ---------- Top-level visible latency when opMode holds (no hazard masking) ----------
/* When the same op is held across cycles, dst must match the launched computation */
assert property (cb past_valid && $past(opMode)==OP_ADD && opMode==OP_ADD |-> dst == $past(srca + srcb));
assert property (cb past_valid && $past(opMode)==OP_SUB && opMode==OP_SUB |-> dst == $past(srca - srcb));
assert property (cb past_valid && $past(opMode)==OP_MUL && opMode==OP_MUL |-> dst == $past(srca * srcb));
assert property (cb past_valid && $past(opMode)==OP_RCP && opMode==OP_RCP |-> dst == $past(ONE_F / srcb));

/* DIV path uses multiplier fed by fpRcpDst; when holding DIV, result must reflect that */
assert property (cb past_valid && $past(opMode)==OP_DIV && opMode==OP_DIV |-> dst == $past(srca * fpRcpDst));

// ---------- X-prop sanity ----------
/* If inputs and opcode are known, output must be known (after first cycle) */
assert property (cb past_valid && !$isunknown({opMode,srca,srcb}) |-> !$isunknown(dst))
  else $error("dst has X/Z with known inputs/opMode");

// ---------- Concise functional coverage ----------
cover property (cb opMode == OP_ADD);
cover property (cb opMode == OP_SUB);
cover property (cb opMode == OP_MUL);
cover property (cb opMode == OP_DIV);
cover property (cb opMode == OP_ABS && srcb[31]);     // ABS negative input
cover property (cb opMode == OP_NEG && srcb != 0);    // NEG non-zero
cover property (cb opMode == OP_RCP);
cover property (cb opMode == OP_SQRT);

/* Exercise DIV pipeline: RCP then DIV across cycles */
sequence rcp_then_div_hold;
  opMode == OP_RCP ##1 opMode == OP_DIV ##1 opMode == OP_DIV;
endsequence
cover property (cb rcp_then_div_hold);

/* Switch between different ops to stress muxing */
cover property (cb (opMode==OP_ADD) ##1 (opMode==OP_SUB) ##1 (opMode==OP_MUL) ##1 (opMode==OP_DIV));

`endif
// pragma translate_on
// synopsys translate_on

`endif // FPU_FP32_SVA
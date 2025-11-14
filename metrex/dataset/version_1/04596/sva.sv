// SVA checker for ExShad32
// Bind this file to the DUT: bind ExShad32 ExShad32_sva u_exshad32_sva(.*);

module ExShad32_sva (
  input logic        clock,
  input logic        reset,
  input logic [31:0] valRs,
  input logic [7:0]  valRt,
  input logic [2:0]  shOp,
  input logic [31:0] valRn
);

  function automatic logic [31:0] sll32 (input logic [31:0] x, input logic [7:0] a);
    return x << a[4:0];
  endfunction
  function automatic logic [31:0] srl32 (input logic [31:0] x, input logic [7:0] a);
    return x >> a[4:0];
  endfunction
  function automatic logic [31:0] sra32 (input logic [31:0] x, input logic [7:0] a);
    return $signed(x) >>> a[4:0];
  endfunction

  // Basic control sanity (avoid X on control/amount)
  assert property (@(posedge clock) disable iff (reset)
    !$isunknown({shOp, valRt[4:0]})
  ) else $error("ExShad32: control/amount has X/Z");

  // Functional checks (combinational, same-cycle)
  // op0 and all unspecified ops -> pass-through
  assert property (@(posedge clock) disable iff (reset)
    (shOp==3'h0 || !(shOp inside {3'h1,3'h2,3'h3,3'h4})) |-> (valRn == valRs)
  ) else $error("ExShad32: pass-through mismatch");

  // op1: logical left
  assert property (@(posedge clock) disable iff (reset)
    (shOp==3'h1) |-> (valRn == sll32(valRs,valRt))
  ) else $error("ExShad32: SLL mismatch (op=1)");

  // op2: behaves identically to op1 in this RTL
  assert property (@(posedge clock) disable iff (reset)
    (shOp==3'h2) |-> (valRn == sll32(valRs,valRt))
  ) else $error("ExShad32: SLL mismatch (op=2 as implemented)");

  // Recommend: amount[7]==0 for left shifts (prevents unintended right behavior)
  assert property (@(posedge clock) disable iff (reset)
    (shOp inside {3'h1,3'h2}) |-> (valRt[7]==1'b0)
  ) else $error("ExShad32: valRt[7] must be 0 for left shifts (op=1/2)");

  // op3: logical right
  assert property (@(posedge clock) disable iff (reset)
    (shOp==3'h3) |-> (valRn == srl32(valRs,valRt))
  ) else $error("ExShad32: SRL mismatch (op=3)");

  // op4: arithmetic right
  assert property (@(posedge clock) disable iff (reset)
    (shOp==3'h4) |-> (valRn == sra32(valRs,valRt))
  ) else $error("ExShad32: SRA mismatch (op=4)");

  // Simple bit-fill sanity for SRL (top bit becomes 0 when shift!=0)
  assert property (@(posedge clock) disable iff (reset)
    (shOp==3'h3 && (valRt[4:0]!=0)) |-> (valRn[31]==1'b0)
  ) else $error("ExShad32: SRL top-fill not zero");

  // Coverage: op variety, boundary amounts, sign for SRA
  covergroup cg_exshad32 @(posedge clock);
    cp_op : coverpoint shOp {
      bins op0  = {3'h0};
      bins sll1 = {3'h1};
      bins sll2 = {3'h2};
      bins srl  = {3'h3};
      bins sra  = {3'h4};
      bins other = {[3'h5:3'h7]};
    }
    cp_amt : coverpoint valRt[4:0] {
      bins zero = {0};
      bins one  = {1};
      bins mid  = {[2:30]};
      bins m31  = {31};
    }
    cp_sign : coverpoint valRs[31];
    cross_sra: cross cp_amt, cp_sign iff (shOp==3'h4);
    cross_op_amt: cross cp_op, cp_amt;
  endgroup
  cg_exshad32 cg_i = new();

endmodule

// Convenient bind
bind ExShad32 ExShad32_sva u_exshad32_sva(
  .clock(clock), .reset(reset),
  .valRs(valRs), .valRt(valRt), .shOp(shOp), .valRn(valRn)
);
// SVA for prioenc/maskunit/allocateunit
// Concise, bindable, parameter-aware. Uses immediate assertions in always_comb for combinational DUTs.

module prioenc_sva #(parameter int REQ_LEN=4, parameter int GRANT_LEN=2)
(
  input  logic [REQ_LEN-1:0]   in,
  input  logic [GRANT_LEN-1:0] out,
  input  logic                 en
);
  // Param sanity
  initial assert ((1<<GRANT_LEN) >= REQ_LEN) else $error("GRANT_LEN too small for REQ_LEN");

  function automatic int unsigned lowest_zero(input logic [REQ_LEN-1:0] v);
    int k; lowest_zero = REQ_LEN;
    for (k=0;k<REQ_LEN;k++) if (!v[k]) begin lowest_zero = k; break; end
  endfunction

  int unsigned idx;
  logic                 exp_en;
  logic [GRANT_LEN-1:0] exp_out;

  always_comb begin
    idx     = lowest_zero(in);
    exp_en  = (idx != REQ_LEN);
    exp_out = exp_en ? idx[GRANT_LEN-1:0] : '0;

    assert (en  == exp_en)  else $error("prioenc en wrong");
    assert (out == exp_out) else $error("prioenc out wrong");
    assert (!en || out < REQ_LEN) else $error("prioenc out out-of-range when enabled");

    // Basic coverage
    cover (en && out == '0);
    cover (en && out == (REQ_LEN-1)[GRANT_LEN-1:0]);
    cover (!en);
  end
endmodule

bind prioenc prioenc_sva #(.REQ_LEN(REQ_LEN), .GRANT_LEN(GRANT_LEN))) prioenc_sva_i
(
  .in(in), .out(out), .en(en)
);


// maskunit: out[i] == 1 for i <= mask, else 0 (independent of input 'in')
module maskunit_sva #(parameter int REQ_LEN=4, parameter int GRANT_LEN=2)
(
  input  logic [GRANT_LEN-1:0] mask,
  input  logic [REQ_LEN-1:0]   in,
  input  logic [REQ_LEN-1:0]   out
);
  initial assert ((1<<GRANT_LEN) >= REQ_LEN) else $error("GRANT_LEN too small for REQ_LEN");

  function automatic logic [REQ_LEN-1:0] expected_mask(input logic [GRANT_LEN-1:0] m);
    logic [REQ_LEN-1:0] r; int k;
    for (k=0;k<REQ_LEN;k++) r[k] = (k <= m);
    return r;
  endfunction

  logic [REQ_LEN-1:0] exp;

  always_comb begin
    exp = expected_mask(mask);
    assert (out == exp) else $error("maskunit out mismatch");
    // Coverage of boundary masks
    cover (mask == '0);
    cover (mask == (REQ_LEN-1)[GRANT_LEN-1:0]);
  end
endmodule

bind maskunit maskunit_sva #(.REQ_LEN(REQ_LEN), .GRANT_LEN(GRANT_LEN))) maskunit_sva_i
(
  .mask(mask), .in(in), .out(out)
);


// allocateunit: two lowest-free indices and allocatable computation
module allocateunit_sva #(parameter int REQ_LEN=4, parameter int GRANT_LEN=2)
(
  input  logic [REQ_LEN-1:0]   busy,
  input  logic                 en1,
  input  logic                 en2,
  input  logic [GRANT_LEN-1:0] free_ent1,
  input  logic [GRANT_LEN-1:0] free_ent2,
  input  logic [1:0]           reqnum,
  input  logic                 allocatable
);
  initial assert ((1<<GRANT_LEN) >= REQ_LEN) else $error("GRANT_LEN too small for REQ_LEN");

  function automatic int unsigned lowest_from(input logic [REQ_LEN-1:0] v, input int unsigned start);
    int k; for (k=start;k<REQ_LEN;k++) if (!v[k]) return k; return REQ_LEN;
  endfunction
  function automatic int unsigned lowest_zero(input logic [REQ_LEN-1:0] v);
    return lowest_from(v, 0);
  endfunction
  function automatic int unsigned count_free(input logic [REQ_LEN-1:0] v);
    int k,c; c=0; for (k=0;k<REQ_LEN;k++) if (!v[k]) c++; return c;
  endfunction

  int unsigned idx1, idx2;
  logic                 exp_en1, exp_en2;
  logic [GRANT_LEN-1:0] exp_e1, exp_e2;

  always_comb begin
    idx1    = lowest_zero(busy);
    idx2    = (idx1==REQ_LEN) ? REQ_LEN : lowest_from(busy, idx1+1);
    exp_en1 = (idx1 != REQ_LEN);
    exp_en2 = (idx2 != REQ_LEN);
    exp_e1  = exp_en1 ? idx1[GRANT_LEN-1:0] : '0;
    exp_e2  = exp_en2 ? idx2[GRANT_LEN-1:0] : '0;

    // Primary correctness
    assert (en1 == exp_en1) else $error("en1 wrong");
    assert (en2 == exp_en2) else $error("en2 wrong");
    assert (free_ent1 == exp_e1) else $error("free_ent1 wrong");
    assert (free_ent2 == exp_e2) else $error("free_ent2 wrong");

    // Sanity/ordering/validity
    assert (!exp_en1 || (busy[free_ent1] == 1'b0)) else $error("free_ent1 not free");
    assert (!exp_en2 || (busy[free_ent2] == 1'b0)) else $error("free_ent2 not free");
    assert (!en2 || (en1 && (free_ent2 > free_ent1))) else $error("free_ent2 must be > free_ent1 when both valid");
    assert (!en1 || free_ent1 < REQ_LEN) else $error("free_ent1 out-of-range");
    assert (!en2 || free_ent2 < REQ_LEN) else $error("free_ent2 out-of-range");

    // Allocatable computation
    logic [2:0] avail;
    avail = {1'b0,en1} + {1'b0,en2};
    assert (allocatable == (reqnum <= avail)) else $error("allocatable mismatch");

    // Coverage: 0/1/2+ free entries; boundary indices; allocatable outcomes
    cover (count_free(busy)==0 && !en1 && !en2);
    cover (count_free(busy)==1 && en1 && !en2);
    cover (count_free(busy)>=2 && en1 && en2);
    cover (en1 && free_ent1=='0);
    cover (en1 && free_ent1==(REQ_LEN-1)[GRANT_LEN-1:0]);
    cover (en2 && free_ent2==(REQ_LEN-1)[GRANT_LEN-1:0]);
    cover (reqnum==2 && allocatable);
    cover (reqnum==2 && !allocatable);
    cover (reqnum==0 && allocatable);
  end
endmodule

bind allocateunit allocateunit_sva #(.REQ_LEN(REQ_LEN), .GRANT_LEN(GRANT_LEN))) allocateunit_sva_i
(
  .busy(busy), .en1(en1), .en2(en2), .free_ent1(free_ent1), .free_ent2(free_ent2),
  .reqnum(reqnum), .allocatable(allocatable)
);
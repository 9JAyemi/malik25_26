// SVA binders for Pipeline and its stages.
// Focus: functional correctness, parameter sanity, X-prop, and concise coverage.

module Stage_sva #(parameter int n=4, parameter int add=1) (
  input logic clk,
  input logic [n-1:0] in,
  input logic [n-1:0] out,
  input logic [n-1:0] reg_out
);
  default clocking @(posedge clk); endclocking
  localparam int unsigned MASKN = (1<<n)-1;

  // Combinational function correct (mod 2^n)
  a_func: assert property ($unsigned(out) == (($unsigned(in)+add) & MASKN));

  // Pipeline register captures current out (observed one cycle later)
  a_regcap: assert property (reg_out == $past(out,1,'0));

  // No X-prop when input is clean
  a_no_x: assert property (!$isunknown(in) |-> !$isunknown(out));

  // Coverage: see both wrap and non-wrap cases at this stage
  c_wrap:  cover property (out < in);       // indicates overflow wrap
  c_nowrap:cover property (out >= in);
endmodule


module Pipeline_sva #(parameter int n=4, m=2, p=3) (
  input logic clk,
  input logic [n-1:0] in,
  input logic [m-1:0] out,
  // tap internal nets
  input logic [n-1:0] stage0_out,
  input logic [n-1:0] stage1_out,
  input logic [n-1:0] stage2_out
);
  default clocking @(posedge clk); endclocking
  localparam int unsigned MASKN = (1<<n)-1;
  localparam int unsigned MASKM = (1<<m)-1;
  localparam int SUM = 1+2+3;

  // Parameter sanity
  initial begin
    if (n <= 0) $fatal(0,"n must be > 0");
    if (m <= 0) $fatal(0,"m must be > 0");
    if (m > n)  $fatal(0,"m must be <= n");
    if (p != 3) $error("p=%0d but design has 3 stages", p);
  end

  // Stage-local functional checks (mod 2^n)
  a_s0: assert property ($unsigned(stage0_out) == (($unsigned(in)+1) & MASKN));
  a_s1: assert property ($unsigned(stage1_out) == (($unsigned(stage0_out)+2) & MASKN));
  a_s2: assert property ($unsigned(stage2_out) == (($unsigned(stage1_out)+3) & MASKN));

  // Output slice correctness (lower m bits only)
  a_slice: assert property ($unsigned(out) == ($unsigned(stage2_out) & MASKM));

  // End-to-end behavior: out == (in+6)[m-1:0]
  a_e2e: assert property ($unsigned(out) ==
                          (((($unsigned(in)+SUM) & MASKN)) & MASKM));

  // Clean in implies clean outs
  a_no_x_s0: assert property (!$isunknown(in) |-> !$isunknown(stage0_out));
  a_no_x_s1: assert property (!$isunknown(in) |-> !$isunknown(stage1_out));
  a_no_x_s2: assert property (!$isunknown(in) |-> !$isunknown(stage2_out));
  a_no_x_out:assert property (!$isunknown(in) |-> !$isunknown(out));

  // Coverage: observe end-to-end wrap and slice dropping upper bits
  c_e2e_wrap: cover property ( (((($unsigned(in)+SUM)&MASKN)&MASKM) == 0) );
  generate if (m < n) begin
    // Hit a case where discarded upper bits are non-zero
    c_slice_drops: cover property ( (((($unsigned(in)+SUM)&MASKN) >> m) != 0) );
  end endgenerate
endmodule


// Bind the assertions into the DUT
bind Stage0 Stage_sva #(.n(n), .add(1)) stage0_sva (.clk(clk), .in(in), .out(out), .reg_out(reg_out));
bind Stage1 Stage_sva #(.n(n), .add(2)) stage1_sva (.clk(clk), .in(in), .out(out), .reg_out(reg_out));
bind Stage2 Stage_sva #(.n(n), .add(3)) stage2_sva (.clk(clk), .in(in), .out(out), .reg_out(reg_out));

bind Pipeline Pipeline_sva #(.n(n), .m(m), .p(p))
  pipeline_sva (.clk(clk), .in(in), .out(out),
                .stage0_out(stage0_out), .stage1_out(stage1_out), .stage2_out(stage2_out));
// SVA for module adder (16-bit combinational adder)
// Bind example (adjust clk/rst as appropriate):
// bind adder adder_sva sva(.clk(clk), .rst_n(rst_n), .A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT));

package adder_sva_pkg;
  checker adder_sva (
    input logic        clk,
    input logic        rst_n,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic        CIN,
    input logic [15:0] SUM,
    input logic        COUT
  );
    default clocking @(posedge clk); endclocking
    default disable iff (!rst_n);

    let ADD = A + B + CIN;

    // Core functional correctness (17-bit sum)
    a_func:  assert property ({COUT, SUM} == ADD);

    // Carry-out equals overflow bit
    a_cout:  assert property (COUT == ADD[16]);

    // LSB sanity (helps debug bit-level issues)
    a_lsb:   assert property (SUM[0] == (A[0] ^ B[0] ^ CIN));

    // Combinational purity (sampled): if inputs stable, outputs stable
    a_pure:  assert property ($stable({A,B,CIN}) |-> $stable({SUM,COUT}));

    // Known-propagation: known-in implies known-out
    a_known: assert property (!$isunknown({A,B,CIN}) |-> !$isunknown({SUM,COUT}));

    // Lightweight coverage (key scenarios and corners)
    cover_cin0:         cover property (CIN==1'b0);
    cover_cin1:         cover property (CIN==1'b1);
    cover_zero:         cover property (A==16'h0000 && B==16'h0000 && CIN==1'b0 && SUM==16'h0000 && COUT==1'b0);
    cover_zero_cin:     cover property (A==16'h0000 && B==16'h0000 && CIN==1'b1 && SUM==16'h0001 && COUT==1'b0);
    cover_max_no_cin:   cover property (A==16'hFFFF && B==16'h0000 && CIN==1'b0 && SUM==16'hFFFF && COUT==1'b0);
    cover_max_plus1:    cover property (A==16'hFFFF && B==16'h0000 && CIN==1'b1 && SUM==16'h0000 && COUT==1'b1);
    cover_both_max:     cover property (A==16'hFFFF && B==16'hFFFF && CIN==1'b0 && SUM==16'hFFFE && COUT==1'b1);
    cover_msb_pair:     cover property (A==16'h8000 && B==16'h8000 && CIN==1'b0 && SUM==16'h0000 && COUT==1'b1);
    cover_overflow:     cover property (COUT==1'b1);
    cover_no_overflow:  cover property (COUT==1'b0);
  endchecker
endpackage
// SVA checker for twos_complement
// Concise properties checking functional correctness, internal consistency, and basic sanity.
// Bind this checker to the DUT.

module twos_complement_sva (
    input  logic [3:0] in,
    input  logic [4:0] out,
    // internal DUT signals (connected by bind inside the DUT scope)
    input  logic [3:0] in_reg,
    input  logic [3:0] neg_in_reg
);

    // Functional spec: out = {sign, magnitude}, where sign=in[3], magnitude=(in[3]? two’s complement of in : in)
    // Use ##0 to align after combinational delta cycles.
    assert property (@(in or out) ##0 out == {in[3], (in[3] ? (~in + 1'b1) : in)})
        else $error("twos_complement: Functional mismatch: in=%0h out=%0h", in, out);

    // Internal register should mirror input combinationally
    assert property (@(in or in_reg) ##0 in_reg == in)
        else $error("twos_complement: in_reg mismatch: in=%0h in_reg=%0h", in, in_reg);

    // Internal negation register definition
    assert property (@(in_reg or neg_in_reg) ##0 neg_in_reg == (~in_reg + 1'b1))
        else $error("twos_complement: neg_in_reg wrong: in_reg=%0h neg_in_reg=%0h", in_reg, neg_in_reg);

    // No-X/Z propagation when inputs are clean
    assert property (@(in or out) (!$isunknown(in)) |-> ##0 !$isunknown(out))
        else $error("twos_complement: X/Z on out with clean in: in=%b out=%b", in, out);

    // Coverage: exercise both branches and key corner cases
    cover property (@(in) in[3] == 1'b0 && ##0 out == {1'b0, in});                     // non-negative path
    cover property (@(in) in[3] == 1'b1 && ##0 out == {1'b1, (~in + 1'b1)});           // negative path
    cover property (@(in) in == 4'h0 && ##0 out == 5'b0_0000);                         // +0
    cover property (@(in) in == 4'h7 && ##0 out == 5'b0_0111);                         // +7
    cover property (@(in) in == 4'h8 && ##0 out == 5'b1_1000);                         // -8 (self two’s complement)
    cover property (@(in) in == 4'hF && ##0 out == 5'b1_0001);                         // -1

endmodule

// Bind into the DUT (place in a package or your testbench)
bind twos_complement twos_complement_sva u_twos_complement_sva (
    .in(in),
    .out(out),
    .in_reg(in_reg),
    .neg_in_reg(neg_in_reg)
);
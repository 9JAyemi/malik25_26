module sysgen_logical_8b7810a2aa_sva (
    input logic d0,
    input logic d1,
    output logic y,
    input logic clk,
    input logic ce,
    input logic clr
);
    // Combinational logic: y is assigned the OR of d0 and d1
    comb_logic: assert property (
        @(posedge clk) disable iff (!clr) (y == (d0 | d1))
    );
endmodule
module dffl_64_sva (
    input logic clk,
    input logic ld,
    input logic rst,
    input logic [63:0] d,
    output logic [63:0] q
);
    // At reset, q should be driven to 0
    reset: assert property (
        @(posedge clk) disable iff (!rst) q == 64'b0
    );

    // When ld is high, q should be driven to the value of d
    load: assert property (
        @(posedge clk) disable iff (!rst) (ld == 1'b1) |-> q == d
    );

    // When ld is low, q should hold its previous value
    no_load: assert property (
        @(posedge clk) disable iff (!rst) (ld == 1'b0) |-> q == q
    );
endmodule
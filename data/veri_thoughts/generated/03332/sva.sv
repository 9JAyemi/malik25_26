module top_module_assertions (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_always_ff
);

    // out_always_ff captures the XOR of a and b on each rising clock edge.
    check_registered_xor: assert property (
        @(posedge clk) 1'b1 |=> (out_always_ff == ($past(a) ^ $past(b)))
    );

    // Sampled input 00 must produce a low output on the next clock.
    check_00_maps_to_zero: assert property (
        @(posedge clk) (!a && !b) |=> (out_always_ff == 1'b0)
    );

    // Sampled input 01 must produce a high output on the next clock.
    check_01_maps_to_one: assert property (
        @(posedge clk) (!a && b) |=> (out_always_ff == 1'b1)
    );

    // Sampled input 10 must produce a high output on the next clock.
    check_10_maps_to_one: assert property (
        @(posedge clk) (a && !b) |=> (out_always_ff == 1'b1)
    );

    // Sampled input 11 must produce a low output on the next clock.
    check_11_maps_to_zero: assert property (
        @(posedge clk) (a && b) |=> (out_always_ff == 1'b0)
    );

endmodule
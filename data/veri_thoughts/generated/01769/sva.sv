module top_module_sva (
    input logic [99:0] a,
    input logic [99:0] b,
    input logic cin,
    input logic cout,
    input logic [99:0] sum
);
    // All properties are sampled on the posedge of cin (no clock/reset in RTL).

    // sum[0] equals a[0] XOR b[0] XOR cin.
    check_sum_bit0: assert property (
        @(posedge cin) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // sum[i] equals a[i] XOR b[i] XOR sum[i-1] for i=1..99.
    genvar gi;
    generate
        for (gi = 1; gi < 100; gi++) begin : g_sum_chain
            check_sum_chain: assert property (
                @(posedge cin) sum[gi] == (a[gi] ^ b[gi] ^ sum[gi-1])
            );
        end
    endgenerate

    // cout equals majority of a[99], b[99], and sum[98].
    check_cout_from_msb: assert property (
        @(posedge cin) cout == ((a[99] & b[99]) | (a[99] & sum[98]) | (b[99] & sum[98]))
    );
endmodule
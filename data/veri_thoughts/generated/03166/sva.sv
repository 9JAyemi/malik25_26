module top_module_sva (
    input logic        clk,
    input logic [99:0] in,
    input logic        q,
    input logic        out_and,
    input logic        out_or,
    input logic        out_xor,
    input logic [7:0]  out_add
);

    // q captures in[0] on each rising edge.
    check_q_captures_in0: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(in[0]))
    );

    // out_and is the reduction AND of in.
    check_out_and_reduction: assert property (
        @(posedge clk) (out_and == (&in))
    );

    // out_or is the reduction OR of in.
    check_out_or_reduction: assert property (
        @(posedge clk) (out_or == (|in))
    );

    // out_xor is the reduction XOR of in.
    check_out_xor_reduction: assert property (
        @(posedge clk) (out_xor == (^in))
    );

    // out_add matches the 3-bit sum of q and the reduction outputs.
    check_out_add_function: assert property (
        @(posedge clk) (out_add == (q + {out_and, out_or, out_xor}))
    );

    // out_add upper bits are always zero.
    check_out_add_upper_zero: assert property (
        @(posedge clk) (out_add[7:3] == 5'b00000)
    );

    // out_add bit 0 is the sum bit of q and out_xor.
    check_out_add_lsb: assert property (
        @(posedge clk) (out_add[0] == (q ^ out_xor))
    );

    // All-ones input has even parity, so out_and implies out_xor is low.
    check_all_ones_even_parity: assert property (
        @(posedge clk) out_and |-> (!out_xor)
    );

    // All-zeros input has zero parity, so no out_or implies no out_xor.
    check_all_zeros_zero_parity: assert property (
        @(posedge clk) (!out_or) |-> (!out_xor)
    );

    // out_add uses the registered in[0] value with current reduction bits.
    check_out_add_uses_registered_in0: assert property (
        @(posedge clk) 1'b1 |=> (out_add == ($past(in[0]) + {out_and, out_or, out_xor}))
    );

endmodule
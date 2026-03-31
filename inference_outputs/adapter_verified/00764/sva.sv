module xor_inv_multiplexer_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sel_b1,
    input logic sel_b2,
    input logic sel_out,
    input logic out_always,
    input logic [3:0] out_xor,
    input logic [3:0] out_xor_inv,
    input logic out_logical_inv
);

// out_xor is the XOR of the selected input with a.
    check_out_xor_function: assert property (
        @(posedge clk) out_xor == ((sel_b2 ? b : (sel_b1 ? b : a)) ^ a)
    );

// out_xor_inv is the bitwise inversion of out_xor.
    check_out_xor_inv_function: assert property (
        @(posedge clk) out_xor_inv == ~out_xor
    );

// out_logical_inv is the logical inversion of out_xor.
    check_out_logical_inv_function: assert property (
        @(posedge clk) out_logical_inv == !out_xor
    );

// When sel_out is high, out_always captures out_logical_inv on the next clock.
    check_out_always_sel_out: assert property (
        @(posedge clk) sel_out |=> (out_always == !out_xor)
    );

// When sel_out is low, out_always captures out_xor_inv on the next clock.
    check_out_always_sel_not_out: assert property (
        @(posedge clk) !sel_out |=> (out_always == ~out_xor)
    );

endmodule

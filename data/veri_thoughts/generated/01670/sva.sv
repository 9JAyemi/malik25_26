module reverse_parity_sva (
    input logic [2:0] in_vec,
    input logic [2:0] out_vec,
    input logic       even_parity
);
    // No explicit clock/reset in RTL; combinational behavior sampled on any in_vec/out_vec/ parity edge.
    // Functional intent: out_vec is bit-reversal of in_vec; even_parity is XOR of in_vec bits.

    // Out vector equals reversed input vector after any input change.
    check_outvec_reverse_on_in_change: assert property (
        @(posedge in_vec[0] or negedge in_vec[0] or
          posedge in_vec[1] or negedge in_vec[1] or
          posedge in_vec[2] or negedge in_vec[2])
        ##0 (out_vec == {in_vec[2], in_vec[1], in_vec[0]})
    );

    // Out vector equals reversed input vector after any output change.
    check_outvec_reverse_on_out_change: assert property (
        @(posedge out_vec[0] or negedge out_vec[0] or
          posedge out_vec[1] or negedge out_vec[1] or
          posedge out_vec[2] or negedge out_vec[2])
        ##0 (out_vec == {in_vec[2], in_vec[1], in_vec[0]})
    );

    // When in_vec[0] changes, out_vec[2] updates to match it.
    check_bitmap_0_to_2: assert property (
        @(posedge in_vec[0] or negedge in_vec[0])
        ##0 (out_vec[2] == in_vec[0])
    );

    // When in_vec[1] changes, out_vec[1] updates to match it.
    check_bitmap_1_to_1: assert property (
        @(posedge in_vec[1] or negedge in_vec[1])
        ##0 (out_vec[1] == in_vec[1])
    );

    // When in_vec[2] changes, out_vec[0] updates to match it.
    check_bitmap_2_to_0: assert property (
        @(posedge in_vec[2] or negedge in_vec[2])
        ##0 (out_vec[0] == in_vec[2])
    );

    // Parity output equals XOR of input bits after any input change.
    check_parity_from_in: assert property (
        @(posedge in_vec[0] or negedge in_vec[0] or
          posedge in_vec[1] or negedge in_vec[1] or
          posedge in_vec[2] or negedge in_vec[2])
        ##0 (even_parity == (in_vec[0] ^ in_vec[1] ^ in_vec[2]))
    );

    // Parity equals XOR of out_vec bits after any output change.
    check_parity_from_out: assert property (
        @(posedge out_vec[0] or negedge out_vec[0] or
          posedge out_vec[1] or negedge out_vec[1] or
          posedge out_vec[2] or negedge out_vec[2])
        ##0 (even_parity == (out_vec[0] ^ out_vec[1] ^ out_vec[2]))
    );

    // On any parity change, it matches XOR of current input bits.
    check_parity_edge_correctness: assert property (
        @(posedge even_parity or negedge even_parity)
        ##0 (even_parity == (in_vec[0] ^ in_vec[1] ^ in_vec[2]))
    );
endmodule
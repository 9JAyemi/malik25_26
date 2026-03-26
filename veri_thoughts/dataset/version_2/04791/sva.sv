module addr_decode_sva (
    input logic [3:0] addr,
    input logic r,
    input logic s,
    input logic t,
    input logic x,
    input logic y,
    input logic z
);

    // Addresses 0001 and 0010 select only r.
    check_r_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b0001) || (addr == 4'b0010)) |-> ({r, s, t, x, y, z} == 6'b100000)
    );

    // Addresses 0011 and 0100 select only s.
    check_s_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b0011) || (addr == 4'b0100)) |-> ({r, s, t, x, y, z} == 6'b010000)
    );

    // Addresses 0101 and 0110 select only t.
    check_t_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b0101) || (addr == 4'b0110)) |-> ({r, s, t, x, y, z} == 6'b001000)
    );

    // Addresses 1000 and 1001 select only x.
    check_x_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b1000) || (addr == 4'b1001)) |-> ({r, s, t, x, y, z} == 6'b000100)
    );

    // Addresses 1010 and 1011 select only y.
    check_y_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b1010) || (addr == 4'b1011)) |-> ({r, s, t, x, y, z} == 6'b000010)
    );

    // Addresses 1100 and 1111 select only z.
    check_z_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b1100) || (addr == 4'b1111)) |-> ({r, s, t, x, y, z} == 6'b000001)
    );

    // Unmapped addresses drive all outputs low.
    check_unmapped_addr_decode: assert property (
        @($global_clock)
        ((addr == 4'b0000) || (addr == 4'b0111) || (addr == 4'b1101) || (addr == 4'b1110))
        |-> ({r, s, t, x, y, z} == 6'b000000)
    );

    // At most one decoded output is high at a time.
    check_outputs_onehot0: assert property (
        @($global_clock)
        $onehot0({r, s, t, x, y, z})
    );

endmodule
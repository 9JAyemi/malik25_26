module binary_adder_sva (
    input logic clk,
    input logic rst_n,

    // DUT ports
    input logic [3:0] a,b,c,d,e,f,g,h,i,
    input logic [2:0] x,y,z,
    input logic ovf,

    // DUT internal signals
    input logic [3:0] xor1, xor2, sum
);
    ///// Combinational definitions /////
    // xor1 equals d XOR e (lower 4 bits of {a,b,c,d} ^ e).
    check_xor1_is_d_xor_e: assert property (
        @(posedge clk) disable iff (!rst_n) xor1 == (d ^ e)
    );
    // xor2 equals i XOR e (lower 4 bits of {f,g,h,i} ^ e).
    check_xor2_is_i_xor_e: assert property (
        @(posedge clk) disable iff (!rst_n) xor2 == (i ^ e)
    );
    // sum equals xor1 + xor2 + e (4-bit result).
    check_sum_definition: assert property (
        @(posedge clk) disable iff (!rst_n) sum == (xor1 + xor2 + e)
    );

    ///// Output mappings /////
    // x is zero-extended LSB of sum.
    check_x_maps_sum0: assert property (
        @(posedge clk) disable iff (!rst_n) x == {2'b00, sum[0]}
    );
    // y is zero-extended bit1 of sum.
    check_y_maps_sum1: assert property (
        @(posedge clk) disable iff (!rst_n) y == {2'b00, sum[1]}
    );
    // z is zero-extended bit2 of sum.
    check_z_maps_sum2: assert property (
        @(posedge clk) disable iff (!rst_n) z == {2'b00, sum[2]}
    );
    // ovf equals MSB of sum.
    check_ovf_maps_sum3: assert property (
        @(posedge clk) disable iff (!rst_n) ovf == sum[3]
    );

    ///// Direct functional checks from inputs /////
    // x[0] matches bit0 of (d^e)+(i^e)+e.
    check_x_lsb_from_inputs: assert property (
        @(posedge clk) disable iff (!rst_n) x[0] == (((d ^ e) + (i ^ e) + e))[0]
    );
    // y[0] matches bit1 of (d^e)+(i^e)+e.
    check_y_bit1_from_inputs: assert property (
        @(posedge clk) disable iff (!rst_n) y[0] == (((d ^ e) + (i ^ e) + e))[1]
    );
    // z[0] matches bit2 of (d^e)+(i^e)+e.
    check_z_bit2_from_inputs: assert property (
        @(posedge clk) disable iff (!rst_n) z[0] == (((d ^ e) + (i ^ e) + e))[2]
    );
    // ovf matches bit3 of (d^e)+(i^e)+e.
    check_ovf_bit3_from_inputs: assert property (
        @(posedge clk) disable iff (!rst_n) ovf == (((d ^ e) + (i ^ e) + e))[3]
    );

    ///// Independence checks /////
    // xor1 unaffected by changes on a,b,c when d and e are stable.
    check_xor1_independent_of_abc: assert property (
        @(posedge clk) disable iff (!rst_n) ($changed({a,b,c}) && $stable({d,e})) |-> $stable(xor1)
    );
    // xor2 unaffected by changes on f,g,h when i and e are stable.
    check_xor2_independent_of_fgh: assert property (
        @(posedge clk) disable iff (!rst_n) ($changed({f,g,h}) && $stable({i,e})) |-> $stable(xor2)
    );
    // sum unaffected by changes on a,b,c,f,g,h when d,e,i are stable.
    check_sum_independent_of_abc_fgh: assert property (
        @(posedge clk) disable iff (!rst_n) ($changed({a,b,c,f,g,h}) && $stable({d,e,i})) |-> $stable(sum)
    );
endmodule
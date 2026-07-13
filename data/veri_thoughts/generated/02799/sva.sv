module little_endian_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [7:0] data_out
);
    // On each clk, data_out equals bit-reverse of prior-cycle data_in.
    check_vector_reverse_map: assert property (
        @(posedge clk) disable iff ($initstate)
            data_out == {
                $past(data_in[0]), $past(data_in[1]), $past(data_in[2]), $past(data_in[3]),
                $past(data_in[4]), $past(data_in[5]), $past(data_in[6]), $past(data_in[7])
            }
    );

    // On each clk, data_out[0] reflects prior-cycle data_in[7].
    check_bit0_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[0] == $past(data_in[7])
    );
    // On each clk, data_out[1] reflects prior-cycle data_in[6].
    check_bit1_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[1] == $past(data_in[6])
    );
    // On each clk, data_out[2] reflects prior-cycle data_in[5].
    check_bit2_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[2] == $past(data_in[5])
    );
    // On each clk, data_out[3] reflects prior-cycle data_in[4].
    check_bit3_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[3] == $past(data_in[4])
    );
    // On each clk, data_out[4] reflects prior-cycle data_in[3].
    check_bit4_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[4] == $past(data_in[3])
    );
    // On each clk, data_out[5] reflects prior-cycle data_in[2].
    check_bit5_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[5] == $past(data_in[2])
    );
    // On each clk, data_out[6] reflects prior-cycle data_in[1].
    check_bit6_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[6] == $past(data_in[1])
    );
    // On each clk, data_out[7] reflects prior-cycle data_in[0].
    check_bit7_map: assert property (
        @(posedge clk) disable iff ($initstate) data_out[7] == $past(data_in[0])
    );

    // If data_in is stable across cycles, data_out remains stable as well.
    check_stable_propagation: assert property (
        @(posedge clk) disable iff ($initstate) $stable(data_in) |-> $stable(data_out)
    );
endmodule
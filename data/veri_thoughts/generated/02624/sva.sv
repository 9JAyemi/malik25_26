module rsdec_syn_m3_sva (
    input logic CLK,
    input logic RESETn,
    input logic [8:0] x,
    input logic [8:0] y
);
    ///// Combinational mapping checks /////
    // y[0] equals x[5].
    map_y0_from_x5: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[0] == x[5])
    );
    // y[1] equals x[6].
    map_y1_from_x6: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[1] == x[6])
    );
    // y[2] equals x[7].
    map_y2_from_x7: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[2] == x[7])
    );
    // y[3] equals x[8].
    map_y3_from_x8: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[3] == x[8])
    );
    // y[4] equals x[0] XOR x[5].
    map_y4_from_x0_x5: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[4] == (x[0] ^ x[5]))
    );
    // y[5] equals x[1] XOR x[6].
    map_y5_from_x1_x6: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[5] == (x[1] ^ x[6]))
    );
    // y[6] equals x[2] XOR x[7].
    map_y6_from_x2_x7: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[6] == (x[2] ^ x[7]))
    );
    // y[7] equals x[3] XOR x[8].
    map_y7_from_x3_x8: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[7] == (x[3] ^ x[8]))
    );
    // y[8] equals x[4].
    map_y8_from_x4: assert property (
        @(posedge CLK) disable iff (!RESETn) (y[8] == x[4])
    );
    // Full vector mapping equals the RTL function.
    map_y_vector: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (y == { x[4], (x[3] ^ x[8]), (x[2] ^ x[7]), (x[1] ^ x[6]), (x[0] ^ x[5]), x[8], x[7], x[6], x[5] })
    );

    ///// Derived consistency checks /////
    // x[0] can be recovered as y[4] XOR y[0].
    recover_x0_via_y4_xor_y0: assert property (
        @(posedge CLK) disable iff (!RESETn) ((y[4] ^ y[0]) == x[0])
    );
    // x[1] can be recovered as y[5] XOR y[1].
    recover_x1_via_y5_xor_y1: assert property (
        @(posedge CLK) disable iff (!RESETn) ((y[5] ^ y[1]) == x[1])
    );
    // x[2] can be recovered as y[6] XOR y[2].
    recover_x2_via_y6_xor_y2: assert property (
        @(posedge CLK) disable iff (!RESETn) ((y[6] ^ y[2]) == x[2])
    );
    // x[3] can be recovered as y[7] XOR y[3].
    recover_x3_via_y7_xor_y3: assert property (
        @(posedge CLK) disable iff (!RESETn) ((y[7] ^ y[3]) == x[3])
    );
endmodule
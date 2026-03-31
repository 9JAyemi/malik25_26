module twos_complement_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] twos_comp
);

// twos_comp equals bitwise NOT of a plus 1.
    check_twos_comp_definition: assert property (
        @(posedge clk) twos_comp == (~a + 4'b0001)
    );

// LSB of twos_comp equals LSB of a.
    check_lsb_preserved: assert property (
        @(posedge clk) twos_comp[0] == a[0]
    );

// twos_comp equals a when a is 0.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (a == 4'b0000) |-> (twos_comp == 4'b0000)
    );

// twos_comp equals 0xF when a is 0.
    check_all_ones_maps_to_all_ones: assert property (
        @(posedge clk) (a == 4'b1111) |-> (twos_comp == 4'b1111)
    );

// twos_comp equals 0 when a equals 0xF.
    check_all_ones_maps_to_zero: assert property (
        @(posedge clk) (a == 4'b1111) |-> (twos_comp == 4'b0000)
    );

// twos_comp equals 0 when a equals 0.
    check_zero_maps_to_all_ones: assert property (
        @(posedge clk) (a == 4'b0000) |-> (twos_comp == 4'b1111)
    );

// twos_comp equals 0xF when a equals 0xF.
    check_all_ones_maps_to_all_ones: assert property (
        @(posedge clk) (a == 4'b1111) |-> (twos_comp == 4'b1111)
    );

// twos_comp equals 0 when a equals 0.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (a == 4'b0000) |-> (twos_comp == 4'b0000)
    );

// twos_comp equals 0xF when a equals 0xF.
    check_all_ones_maps_to_all_ones: assert property (
        @(posedge clk) (a == 4'b1111) |-> (twos_comp == 4'b1111)
    );

endmodule

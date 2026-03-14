module td_mode_generator_sva (
    input logic clk,
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);
    // When ctrl[8:6]==000, td_mode must be 0000.
    check_map_000: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b000) |-> (td_mode == 4'b0000)
    );
    // When ctrl[8:6]==001, td_mode must be 1000.
    check_map_001: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b001) |-> (td_mode == 4'b1000)
    );
    // When ctrl[8:6]==010, td_mode must be 0100.
    check_map_010: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b010) |-> (td_mode == 4'b0100)
    );
    // When ctrl[8:6]==011, td_mode must be 1100.
    check_map_011: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b011) |-> (td_mode == 4'b1100)
    );
    // When ctrl[8:6]==100, td_mode must be 0010.
    check_map_100: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b100) |-> (td_mode == 4'b0010)
    );
    // When ctrl[8:6]==101, td_mode must be 1010.
    check_map_101: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b101) |-> (td_mode == 4'b1010)
    );
    // When ctrl[8:6]==110, td_mode must be 0101.
    check_map_110: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b110) |-> (td_mode == 4'b0101)
    );
    // When ctrl[8:6]==111, td_mode must be 1111.
    check_map_111: assert property (
        @(posedge clk) (ctrl[8:6] == 3'b111) |-> (td_mode == 4'b1111)
    );

    // td_mode[3] equals ctrl[6] for all encodings.
    check_bit3_matches_ctrl6: assert property (
        @(posedge clk) td_mode[3] == ctrl[6]
    );
    // td_mode[2] equals ctrl[7] for all encodings.
    check_bit2_matches_ctrl7: assert property (
        @(posedge clk) td_mode[2] == ctrl[7]
    );
    // td_mode[1] equals ctrl[8] & (~ctrl[7] | ctrl[6]).
    check_bit1_function: assert property (
        @(posedge clk) td_mode[1] == (ctrl[8] & (~ctrl[7] | ctrl[6]))
    );
    // td_mode[0] equals ctrl[8] & ctrl[7].
    check_bit0_is_and: assert property (
        @(posedge clk) td_mode[0] == (ctrl[8] & ctrl[7])
    );
endmodule
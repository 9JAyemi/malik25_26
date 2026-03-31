module sector_flash_map_sva (
    input logic [2:0] sector,
    input logic [2:0] flash_sector
);

    // Sector 1 maps to 000.
    check_sector1_map: assert property (
        @($global_clock) (sector == 3'd1) |-> (flash_sector == 3'b000)
    );

    // Sector 2 maps to 001.
    check_sector2_map: assert property (
        @($global_clock) (sector == 3'd2) |-> (flash_sector == 3'b001)
    );

    // Sector 3 maps to 010.
    check_sector3_map: assert property (
        @($global_clock) (sector == 3'd3) |-> (flash_sector == 3'b010)
    );

    // Sector 4 maps to 011.
    check_sector4_map: assert property (
        @($global_clock) (sector == 3'd4) |-> (flash_sector == 3'b011)
    );

    // Sector 5 maps to 100.
    check_sector5_map: assert property (
        @($global_clock) (sector == 3'd5) |-> (flash_sector == 3'b100)
    );

    // Any unmapped sector ID drives 000.
    check_default_zero: assert property (
        @($global_clock)
        ((sector != 3'd1) && (sector != 3'd2) && (sector != 3'd3) &&
         (sector != 3'd4) && (sector != 3'd5)) |-> (flash_sector == 3'b000)
    );

endmodule
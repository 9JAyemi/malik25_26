module sector_flash_map_sva (
    input logic clk,
    input logic [2:0] sector,
    input logic [2:0] flash_sector
);

// Sector 1 maps to 000.
    check_sector1_maps_to_000: assert property (
        @(posedge clk) (sector == 3'd1) |-> (flash_sector == 3'b000)
    );

// Sector 2 maps to 001.
    check_sector2_maps_to_001: assert property (
        @(posedge clk) (sector == 3'd2) |-> (flash_sector == 3'b001)
    );

// Sector 3 maps to 010.
    check_sector3_maps_to_010: assert property (
        @(posedge clk) (sector == 3'd3) |-> (flash_sector == 3'b010)
    );

// Sector 4 maps to 011.
    check_sector4_maps_to_011: assert property (
        @(posedge clk) (sector == 3'd4) |-> (flash_sector == 3'b011)
    );

// Sector 5 maps to 100.
    check_sector5_maps_to_100: assert property (
        @(posedge clk) (sector == 3'd5) |-> (flash_sector == 3'b100)
    );

// Invalid sector IDs (6..7) map to 000.
    check_invalid_sectors_map_to_000: assert property (
        @(posedge clk) (sector >= 3'd6) |-> (flash_sector == 3'b000)
    );

// Output is always one of the five encoded values.
    check_output_encoding_legal: assert property (
        @(posedge clk) flash_sector inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100}
    );

endmodule

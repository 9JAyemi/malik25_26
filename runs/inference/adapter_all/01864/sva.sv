module sector_flash_map_sva (
    input logic [2:0] sector,
    input logic [2:0] flash_sector
);
    // For sector 1, flash_sector must be 000.
    map_sector1: assert property (
        @(posedge sector[0]) (sector == 3'd1) |-> (flash_sector == 3'b000)
    );

    // For sector 2, flash_sector must be 001.
    map_sector2: assert property (
        @(posedge sector[0]) (sector == 3'd2) |-> (flash_sector == 3'b001)
    );

    // For sector 3, flash_sector must be 010.
    map_sector3: assert property (
        @(posedge sector[0]) (sector == 3'd3) |-> (flash_sector == 3'b010)
    );

    // For sector 4, flash_sector must be 011.
    map_sector4: assert property (
        @(posedge sector[0]) (sector == 3'd4) |-> (flash_sector == 3'b011)
    );

    // For sector 5, flash_sector must be 100.
    map_sector5: assert property (
        @(posedge sector[0]) (sector == 3'd5) |-> (flash_sector == 3'b100)
    );

    // For invalid sector IDs (6..7), flash_sector must be 000.
    map_invalid_zero: assert property (
        @(posedge sector[0]) (sector >= 3'd6) |-> (flash_sector == 3'b000)
    );

    // flash_sector must never be 101, 110, or 111.
    check_no_reserved_values: assert property (
        @(posedge sector[0]) (flash_sector != 3'b101) && (flash_sector != 3'b110) && (flash_sector != 3'b111)
    );

    // If flash_sector is 001, sector must be 2.
    reverse_map_sector2: assert property (
        @(posedge sector[0]) (flash_sector == 3'b001) |-> (sector == 3'd2)
    );

    // If flash_sector is 010, sector must be 3.
    reverse_map_sector3: assert property (
        @(posedge sector[0]) (flash_sector == 3'b010) |-> (sector == 3'd3)
    );

    // If flash_sector is 011, sector must be 4.
    reverse_map_sector4: assert property (
        @(posedge sector[0]) (flash_sector == 3'b011) |-> (sector == 3'd4)
    );

    // If flash_sector is 100, sector must be 5.
    reverse_map_sector5: assert property (
        @(posedge sector[0]) (flash_sector == 3'b100) |-> (sector == 3'd5)
    );
endmodule
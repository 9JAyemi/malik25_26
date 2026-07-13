module sector_flash_map_sva (
    input logic flash_sector,
    input logic sector,
    input logic b000,
    input logic b001,
    input logic b010,
    input logic b011,
    input logic b100,
    input logic clk_in_1,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic d4,
    input logic d5
);

property ValidSecteotid; @(posedge clk_in_1) (sector) == (3'd1) |-> (flash_sector) == (3'b000); endproperty
assert property (ValidSecteotid);

property ValidSecteotid_2; @(posedge clk_in_1) (sector) == (3'd2) |-> (flash_sector) == (3'b001); endproperty
assert property (ValidSecteotid_2);

property ValidSecteotid_3; @(posedge clk_in_1) (sector) == (3'd3) |-> (flash_sector) == (3'b010); endproperty
assert property (ValidSecteotid_3);

property ValidSecteotid_4; @(posedge clk_in_1) (sector) == (3'd4) |-> (flash_sector) == (3'b011); endproperty
assert property (ValidSecteotid_4);

property ValidSecteotid_5; @(posedge clk_in_1) (sector) == (3'd5) |-> (flash_sector) == (3'b100); endproperty
assert property (ValidSecteotid_5);

property ValidSecteotid_6; @(posedge clk_in_1) (sector) != 3'd1 && (sector) != 3'd2 && (sector) != 3'd3 && (sector) != 3'd4 && (sector) != 3'd5  |-> (flash_sector) == 3'b000; endproperty
assert property (ValidSecteotid_6);

endmodule
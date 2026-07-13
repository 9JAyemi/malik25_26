module rominfr_sva (
    input logic clk,
    input logic en,
    input logic [4:0] addr,
    input logic [3:0] data
);

    // When enabled, address 00000 loads 0010 on the next cycle.
    check_addr_00000_load: assert property (
        @(posedge clk) en && (addr == 5'b00000) |=> (data == 4'b0010)
    );

    // When enabled, address 00001 loads 0010 on the next cycle.
    check_addr_00001_load: assert property (
        @(posedge clk) en && (addr == 5'b00001) |=> (data == 4'b0010)
    );

    // When enabled, address 00010 loads 1110 on the next cycle.
    check_addr_00010_load: assert property (
        @(posedge clk) en && (addr == 5'b00010) |=> (data == 4'b1110)
    );

    // When enabled, address 00011 loads 0010 on the next cycle.
    check_addr_00011_load: assert property (
        @(posedge clk) en && (addr == 5'b00011) |=> (data == 4'b0010)
    );

    // When enabled, address 00100 loads 0100 on the next cycle.
    check_addr_00100_load: assert property (
        @(posedge clk) en && (addr == 5'b00100) |=> (data == 4'b0100)
    );

    // When enabled, address 00101 loads 1010 on the next cycle.
    check_addr_00101_load: assert property (
        @(posedge clk) en && (addr == 5'b00101) |=> (data == 4'b1010)
    );

    // When enabled, address 00110 loads 1100 on the next cycle.
    check_addr_00110_load: assert property (
        @(posedge clk) en && (addr == 5'b00110) |=> (data == 4'b1100)
    );

    // When enabled, address 00111 loads 0000 on the next cycle.
    check_addr_00111_load: assert property (
        @(posedge clk) en && (addr == 5'b00111) |=> (data == 4'b0000)
    );

    // When enabled, address 01000 loads 1010 on the next cycle.
    check_addr_01000_load: assert property (
        @(posedge clk) en && (addr == 5'b01000) |=> (data == 4'b1010)
    );

    // When enabled, address 01001 loads 0010 on the next cycle.
    check_addr_01001_load: assert property (
        @(posedge clk) en && (addr == 5'b01001) |=> (data == 4'b0010)
    );

    // When enabled, address 01010 loads 1110 on the next cycle.
    check_addr_01010_load: assert property (
        @(posedge clk) en && (addr == 5'b01010) |=> (data == 4'b1110)
    );

    // When enabled, address 01011 loads 0010 on the next cycle.
    check_addr_01011_load: assert property (
        @(posedge clk) en && (addr == 5'b01011) |=> (data == 4'b0010)
    );

    // When enabled, address 01100 loads 0100 on the next cycle.
    check_addr_01100_load: assert property (
        @(posedge clk) en && (addr == 5'b01100) |=> (data == 4'b0100)
    );

    // When enabled, address 01101 loads 1010 on the next cycle.
    check_addr_01101_load: assert property (
        @(posedge clk) en && (addr == 5'b01101) |=> (data == 4'b1010)
    );

    // When enabled, address 01110 loads 1100 on the next cycle.
    check_addr_01110_load: assert property (
        @(posedge clk) en && (addr == 5'b01110) |=> (data == 4'b1100)
    );

    // When enabled, address 01111 loads 0000 on the next cycle.
    check_addr_01111_load: assert property (
        @(posedge clk) en && (addr == 5'b01111) |=> (data == 4'b0000)
    );

    // When disabled, data holds its previous value.
    check_disabled_hold: assert property (
        @(posedge clk) !en |=> (data == $past(data))
    );

endmodule
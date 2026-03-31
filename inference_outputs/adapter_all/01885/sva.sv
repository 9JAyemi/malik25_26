module rominfr_sva (
    input logic clk,
    input logic en,
    input logic [4:0] addr,
    input logic [3:0] data
);

    // Address 00000 loads 0010 on the next clock.
    check_addr_00000_loads_0010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00000)) |=> (data == 4'b0010)
    );

    // Address 00001 loads 0010 on the next clock.
    check_addr_00001_loads_0010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00001)) |=> (data == 4'b0010)
    );

    // Address 00010 loads 1110 on the next clock.
    check_addr_00010_loads_1110: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00010)) |=> (data == 4'b1110)
    );

    // Address 00011 loads 0010 on the next clock.
    check_addr_00011_loads_0010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00011)) |=> (data == 4'b0010)
    );

    // Address 00100 loads 0100 on the next clock.
    check_addr_00100_loads_0100: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00100)) |=> (data == 4'b0100)
    );

    // Address 00101 loads 1010 on the next clock.
    check_addr_00101_loads_1010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00101)) |=> (data == 4'b1010)
    );

    // Address 00110 loads 1100 on the next clock.
    check_addr_00110_loads_1100: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00110)) |=> (data == 4'b1100)
    );

    // Address 00111 loads 0000 on the next clock.
    check_addr_00111_loads_0000: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b00111)) |=> (data == 4'b0000)
    );

    // Address 01000 loads 1010 on the next clock.
    check_addr_01000_loads_1010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01000)) |=> (data == 4'b1010)
    );

    // Address 01001 loads 0010 on the next clock.
    check_addr_01001_loads_0010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01001)) |=> (data == 4'b0010)
    );

    // Address 01010 loads 1110 on the next clock.
    check_addr_01010_loads_1110: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01010)) |=> (data == 4'b1110)
    );

    // Address 01011 loads 0010 on the next clock.
    check_addr_01011_loads_0010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01011)) |=> (data == 4'b0010)
    );

    // Address 01100 loads 0100 on the next clock.
    check_addr_01100_loads_0100: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01100)) |=> (data == 4'b0100)
    );

    // Address 01101 loads 1010 on the next clock.
    check_addr_01101_loads_1010: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01101)) |=> (data == 4'b1010)
    );

    // Address 01110 loads 1100 on the next clock.
    check_addr_01110_loads_1100: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01110)) |=> (data == 4'b1100)
    );

    // Address 01111 loads 0000 on the next clock.
    check_addr_01111_loads_0000: assert property (
        @(posedge clk) disable iff (1'b0)
        (en && (addr == 5'b01111)) |=> (data == 4'b0000)
    );

    // With enable low, the register holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (1'b0)
        (!en) |=> (data == $past(data))
    );

endmodule
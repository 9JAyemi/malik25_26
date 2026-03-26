module maprom1_sva(
    input logic clk,
    input logic en,
    input logic [3:0] addr,
    input logic [7:0] data
);

    // When disabled, data holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) !en |=> $stable(data)
    );

    // Enabled address 0 maps to 8'hFF.
    check_addr_0_map: assert property (
        @(posedge clk) (en && (addr == 4'h0)) |=> (data == 8'hFF)
    );

    // Enabled address 1 maps to 8'h81.
    check_addr_1_map: assert property (
        @(posedge clk) (en && (addr == 4'h1)) |=> (data == 8'h81)
    );

    // Enabled address 2 maps to 8'hEF.
    check_addr_2_map: assert property (
        @(posedge clk) (en && (addr == 4'h2)) |=> (data == 8'hEF)
    );

    // Enabled address 3 maps to 8'h64.
    check_addr_3_map: assert property (
        @(posedge clk) (en && (addr == 4'h3)) |=> (data == 8'h64)
    );

    // Enabled address 4 maps to 8'hF7.
    check_addr_4_map: assert property (
        @(posedge clk) (en && (addr == 4'h4)) |=> (data == 8'hF7)
    );

    // Enabled address 5 maps to 8'h11.
    check_addr_5_map: assert property (
        @(posedge clk) (en && (addr == 4'h5)) |=> (data == 8'h11)
    );

    // Enabled address 6 maps to 8'hF7.
    check_addr_6_map: assert property (
        @(posedge clk) (en && (addr == 4'h6)) |=> (data == 8'hF7)
    );

    // Enabled address 7 maps to 8'h8C.
    check_addr_7_map: assert property (
        @(posedge clk) (en && (addr == 4'h7)) |=> (data == 8'h8C)
    );

    // Enabled address 8 maps to 8'h08.
    check_addr_8_map: assert property (
        @(posedge clk) (en && (addr == 4'h8)) |=> (data == 8'h08)
    );

    // Enabled address 9 maps to 8'h3C.
    check_addr_9_map: assert property (
        @(posedge clk) (en && (addr == 4'h9)) |=> (data == 8'h3C)
    );

    // Enabled addresses A-F map to 8'h00.
    check_default_map: assert property (
        @(posedge clk)
        (en && ((addr == 4'hA) || (addr == 4'hB) || (addr == 4'hC) ||
                (addr == 4'hD) || (addr == 4'hE) || (addr == 4'hF)))
        |=> (data == 8'h00)
    );

endmodule
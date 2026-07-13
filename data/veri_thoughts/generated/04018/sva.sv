module pcmb_tables_sva(
    input logic [3:0] TABLE_B1_ADDR,
    input logic [4:0] TABLE_B1_OUT,
    input logic [2:0] TABLE_B2_ADDR,
    input logic [7:0] TABLE_B2_OUT
);
    // No RTL clock or reset; use a formal sampling clock.
    (* gclk *) logic clk;

    // TABLE_B1 lower-half address changes map to positive odd values.
    check_b1_lower_half_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B1_ADDR) && !TABLE_B1_ADDR[3]) |-> (TABLE_B1_OUT == {TABLE_B1_ADDR, 1'b1})
    );

    // TABLE_B1 upper-half address changes map to negative odd values.
    check_b1_upper_half_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B1_ADDR) && TABLE_B1_ADDR[3]) |-> (TABLE_B1_OUT == {1'b1, ~TABLE_B1_ADDR[2:0], 1'b1})
    );

    // TABLE_B1 output only depends on TABLE_B1_ADDR.
    check_b1_output_stable_when_addr_stable: assert property (
        @(posedge clk)
        $stable(TABLE_B1_ADDR) |-> $stable(TABLE_B1_OUT)
    );

    // Any updated TABLE_B1 value remains odd.
    check_b1_output_is_odd_on_addr_change: assert property (
        @(posedge clk)
        $changed(TABLE_B1_ADDR) |-> (TABLE_B1_OUT[0] == 1'b1)
    );

    // Any updated TABLE_B1 sign bit matches the address MSB.
    check_b1_sign_matches_addr_msb_on_addr_change: assert property (
        @(posedge clk)
        $changed(TABLE_B1_ADDR) |-> (TABLE_B1_OUT[4] == TABLE_B1_ADDR[3])
    );

    // TABLE_B2 address changes into 0 through 3 map to 57.
    check_b2_low_group_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B2_ADDR) && (TABLE_B2_ADDR <= 3'h3)) |-> (TABLE_B2_OUT == 8'd57)
    );

    // TABLE_B2 address 4 maps to 77.
    check_b2_addr4_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B2_ADDR) && (TABLE_B2_ADDR == 3'h4)) |-> (TABLE_B2_OUT == 8'd77)
    );

    // TABLE_B2 address 5 maps to 102.
    check_b2_addr5_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B2_ADDR) && (TABLE_B2_ADDR == 3'h5)) |-> (TABLE_B2_OUT == 8'd102)
    );

    // TABLE_B2 address 6 maps to 128.
    check_b2_addr6_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B2_ADDR) && (TABLE_B2_ADDR == 3'h6)) |-> (TABLE_B2_OUT == 8'd128)
    );

    // TABLE_B2 address 7 maps to 153.
    check_b2_addr7_mapping: assert property (
        @(posedge clk)
        ($changed(TABLE_B2_ADDR) && (TABLE_B2_ADDR == 3'h7)) |-> (TABLE_B2_OUT == 8'd153)
    );

    // TABLE_B2 output only depends on TABLE_B2_ADDR.
    check_b2_output_stable_when_addr_stable: assert property (
        @(posedge clk)
        $stable(TABLE_B2_ADDR) |-> $stable(TABLE_B2_OUT)
    );

endmodule
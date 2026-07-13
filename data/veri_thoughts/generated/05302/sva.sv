module system_axi_uartlite_0_0_pselect_f_sva (
    input logic clk,
    input logic ce_expnd_i_3,
    input logic bus2ip_addr_i_reg_2,
    input logic start2,
    input logic bus2ip_addr_i_reg_3
);

    // Output matches the RTL three-input AND.
    check_ce_expnd_matches_and: assert property (
        @(posedge clk)
        ce_expnd_i_3 == (bus2ip_addr_i_reg_2 & start2 & bus2ip_addr_i_reg_3)
    );

    // A high output requires all three inputs to be high.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk)
        ce_expnd_i_3 |-> (bus2ip_addr_i_reg_2 && start2 && bus2ip_addr_i_reg_3)
    );

    // All three high inputs drive the output high.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk)
        (bus2ip_addr_i_reg_2 && start2 && bus2ip_addr_i_reg_3) |-> ce_expnd_i_3
    );

    // A low bus2ip_addr_i_reg_2 forces the output low.
    check_addr2_low_drives_output_low: assert property (
        @(posedge clk)
        !bus2ip_addr_i_reg_2 |-> !ce_expnd_i_3
    );

    // A low start2 forces the output low.
    check_start2_low_drives_output_low: assert property (
        @(posedge clk)
        !start2 |-> !ce_expnd_i_3
    );

    // A low bus2ip_addr_i_reg_3 forces the output low.
    check_addr3_low_drives_output_low: assert property (
        @(posedge clk)
        !bus2ip_addr_i_reg_3 |-> !ce_expnd_i_3
    );

endmodule
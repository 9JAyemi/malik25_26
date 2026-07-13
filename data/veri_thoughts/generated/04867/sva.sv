module sys_led_module_sva (
    input logic       led_clk,
    input logic       led_rst_n,
    input logic [7:0] led_in,
    input logic [7:0] led_out,
    input logic [9:0] led_cnt
);

    // Clock: led_clk
    // Reset: led_rst_n is active low
    // Logic: mixed counter state and combinational LED decoding

    // A held active-low reset keeps the counter at zero.
    check_led_cnt_hold_in_reset: assert property (
        @(posedge led_clk) disable iff ($initstate)
        (!$past(led_rst_n) && !led_rst_n) |-> (led_cnt == 10'd0)
    );

    // A held active-low reset keeps the counter-driven outputs low.
    check_led_out_hold_in_reset: assert property (
        @(posedge led_clk) disable iff ($initstate)
        (!$past(led_rst_n) && !led_rst_n) |-> (led_out[7:4] == 4'b0000)
    );

    // After reset release, the sampled counter is still zero until the next clock update.
    check_led_cnt_after_reset_release: assert property (
        @(posedge led_clk) disable iff ($initstate)
        (!$past(led_rst_n) && led_rst_n) |-> (led_cnt == 10'd0)
    );

    // After reset release, the sampled counter-driven outputs are still low until the next clock update.
    check_led_out_after_reset_release: assert property (
        @(posedge led_clk) disable iff ($initstate)
        (!$past(led_rst_n) && led_rst_n) |-> (led_out[7:4] == 4'b0000)
    );

    // led_out[0] is the reduction AND of led_in.
    check_led_out0_and: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[0] == (&led_in))
    );

    // led_out[1] is the reduction OR of led_in.
    check_led_out1_or: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[1] == (|led_in))
    );

    // led_out[2] is the inverted reduction AND of led_in.
    check_led_out2_nand: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[2] == (~&led_in))
    );

    // led_out[3] is the inverted reduction OR of led_in.
    check_led_out3_nor: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[3] == (~|led_in))
    );

    // led_out[4] mirrors counter bit 6.
    check_led_out4_cnt6: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[4] == led_cnt[6])
    );

    // led_out[5] mirrors counter bit 7.
    check_led_out5_cnt7: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[5] == led_cnt[7])
    );

    // led_out[6] mirrors counter bit 8.
    check_led_out6_cnt8: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[6] == led_cnt[8])
    );

    // led_out[7] mirrors counter bit 9.
    check_led_out7_cnt9: assert property (
        @(posedge led_clk) disable iff (!led_rst_n)
        (led_out[7] == led_cnt[9])
    );

endmodule

bind sys_led_module sys_led_module_sva sys_led_module_sva_inst (.*);
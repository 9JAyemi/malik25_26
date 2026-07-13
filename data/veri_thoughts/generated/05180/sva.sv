module Device_GPIO_7seg_sva (
    input logic        clk,
    input logic        rst,
    input logic        GPIOfffffe00_we,
    input logic [2:0]  Test,
    input logic [31:0] disp_cpudata,
    input logic [31:0] Test_data0,
    input logic [31:0] Test_data1,
    input logic [31:0] Test_data2,
    input logic [31:0] Test_data3,
    input logic [31:0] Test_data4,
    input logic [31:0] Test_data5,
    input logic [31:0] Test_data6,
    input logic [31:0] disp_num
);

    // While reset is asserted, disp_num stays at the reset constant.
    check_reset_value: assert property (
        @(negedge clk) disable iff (!rst)
        1'b1 |-> (disp_num == 32'hAA5555AA)
    );

    // In Test 0 with write enable, disp_num loads disp_cpudata on the next clock.
    check_test0_cpu_write_load: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd0 && GPIOfffffe00_we) |=> (disp_num == $past(disp_cpudata))
    );

    // In Test 0 without write enable, disp_num holds its previous value.
    check_test0_hold_without_write: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd0 && !GPIOfffffe00_we) |=> (disp_num == $past(disp_num))
    );

    // In Test 1, disp_num loads Test_data0 on the next clock.
    check_test1_selects_data0: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd1) |=> (disp_num == $past(Test_data0))
    );

    // In Test 2, disp_num loads Test_data1 on the next clock.
    check_test2_selects_data1: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd2) |=> (disp_num == $past(Test_data1))
    );

    // In Test 3, disp_num loads Test_data2 on the next clock.
    check_test3_selects_data2: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd3) |=> (disp_num == $past(Test_data2))
    );

    // In Test 4, disp_num loads Test_data3 on the next clock.
    check_test4_selects_data3: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd4) |=> (disp_num == $past(Test_data3))
    );

    // In Test 5, disp_num loads Test_data4 on the next clock.
    check_test5_selects_data4: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd5) |=> (disp_num == $past(Test_data4))
    );

    // In Test 6, disp_num loads Test_data5 on the next clock.
    check_test6_selects_data5: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd6) |=> (disp_num == $past(Test_data5))
    );

    // In Test 7, disp_num loads Test_data6 on the next clock.
    check_test7_selects_data6: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd7) |=> (disp_num == $past(Test_data6))
    );

endmodule
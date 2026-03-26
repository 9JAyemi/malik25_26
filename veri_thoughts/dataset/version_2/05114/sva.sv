module seven_seg_Dev_IO_sva(
    input logic clk,
    input logic rst,
    input logic GPIOe0000000_we,
    input logic [2:0] Test,
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

    // Reset drives disp_num to zero.
    check_reset_clears_disp_num: assert property (
        @(negedge clk)
        rst |=> (disp_num == 32'h0000_0000)
    );

    // Test==0 with write low holds the previous value.
    check_hold_when_test0_no_write: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd0 && !GPIOe0000000_we) |=> (disp_num == $past(disp_num))
    );

    // Test==0 with write high loads disp_cpudata.
    check_load_cpudata_when_test0_write: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd0 && GPIOe0000000_we) |=> (disp_num == $past(disp_cpudata))
    );

    // Test==1 loads Test_data0.
    check_load_test_data0: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd1) |=> (disp_num == $past(Test_data0))
    );

    // Test==2 loads Test_data1.
    check_load_test_data1: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd2) |=> (disp_num == $past(Test_data1))
    );

    // Test==3 loads Test_data2.
    check_load_test_data2: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd3) |=> (disp_num == $past(Test_data2))
    );

    // Test==4 loads Test_data3.
    check_load_test_data3: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd4) |=> (disp_num == $past(Test_data3))
    );

    // Test==5 loads Test_data4.
    check_load_test_data4: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd5) |=> (disp_num == $past(Test_data4))
    );

    // Test==6 loads Test_data5.
    check_load_test_data5: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd6) |=> (disp_num == $past(Test_data5))
    );

    // Test==7 loads Test_data6.
    check_load_test_data6: assert property (
        @(negedge clk) disable iff (rst)
        (Test == 3'd7) |=> (disp_num == $past(Test_data6))
    );

endmodule
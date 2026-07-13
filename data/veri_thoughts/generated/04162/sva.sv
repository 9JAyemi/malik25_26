module mux32_sva(
    input logic clk,
    input logic [4:0] select,
    input logic [7:0] data_i00,
    input logic [7:0] data_i01,
    input logic [7:0] data_i02,
    input logic [7:0] data_i03,
    input logic [7:0] data_i04,
    input logic [7:0] data_i05,
    input logic [7:0] data_i06,
    input logic [7:0] data_i07,
    input logic [7:0] data_i08,
    input logic [7:0] data_i09,
    input logic [7:0] data_i10,
    input logic [7:0] data_i11,
    input logic [7:0] data_i12,
    input logic [7:0] data_i13,
    input logic [7:0] data_i14,
    input logic [7:0] data_i15,
    input logic [7:0] data_i16,
    input logic [7:0] data_i17,
    input logic [7:0] data_i18,
    input logic [7:0] data_i19,
    input logic [7:0] data_i20,
    input logic [7:0] data_i21,
    input logic [7:0] data_i22,
    input logic [7:0] data_i23,
    input logic [7:0] data_i24,
    input logic [7:0] data_i25,
    input logic [7:0] data_i26,
    input logic [7:0] data_i27,
    input logic [7:0] data_i28,
    input logic [7:0] data_i29,
    input logic [7:0] data_i30,
    input logic [7:0] data_i31,
    input logic [7:0] data_o
);

    // select 0 routes data_i00 to data_o.
    check_select_00_routes_data_i00: assert property (
        @(posedge clk) (select == 5'd0) |-> (data_o == data_i00)
    );

    // select 1 routes data_i01 to data_o.
    check_select_01_routes_data_i01: assert property (
        @(posedge clk) (select == 5'd1) |-> (data_o == data_i01)
    );

    // select 2 routes data_i02 to data_o.
    check_select_02_routes_data_i02: assert property (
        @(posedge clk) (select == 5'd2) |-> (data_o == data_i02)
    );

    // select 3 routes data_i03 to data_o.
    check_select_03_routes_data_i03: assert property (
        @(posedge clk) (select == 5'd3) |-> (data_o == data_i03)
    );

    // select 4 routes data_i04 to data_o.
    check_select_04_routes_data_i04: assert property (
        @(posedge clk) (select == 5'd4) |-> (data_o == data_i04)
    );

    // select 5 routes data_i05 to data_o.
    check_select_05_routes_data_i05: assert property (
        @(posedge clk) (select == 5'd5) |-> (data_o == data_i05)
    );

    // select 6 routes data_i06 to data_o.
    check_select_06_routes_data_i06: assert property (
        @(posedge clk) (select == 5'd6) |-> (data_o == data_i06)
    );

    // select 7 routes data_i07 to data_o.
    check_select_07_routes_data_i07: assert property (
        @(posedge clk) (select == 5'd7) |-> (data_o == data_i07)
    );

    // select 8 routes data_i08 to data_o.
    check_select_08_routes_data_i08: assert property (
        @(posedge clk) (select == 5'd8) |-> (data_o == data_i08)
    );

    // select 9 routes data_i09 to data_o.
    check_select_09_routes_data_i09: assert property (
        @(posedge clk) (select == 5'd9) |-> (data_o == data_i09)
    );

    // select 10 routes data_i10 to data_o.
    check_select_10_routes_data_i10: assert property (
        @(posedge clk) (select == 5'd10) |-> (data_o == data_i10)
    );

    // select 11 routes data_i11 to data_o.
    check_select_11_routes_data_i11: assert property (
        @(posedge clk) (select == 5'd11) |-> (data_o == data_i11)
    );

    // select 12 routes data_i12 to data_o.
    check_select_12_routes_data_i12: assert property (
        @(posedge clk) (select == 5'd12) |-> (data_o == data_i12)
    );

    // select 13 routes data_i13 to data_o.
    check_select_13_routes_data_i13: assert property (
        @(posedge clk) (select == 5'd13) |-> (data_o == data_i13)
    );

    // select 14 routes data_i14 to data_o.
    check_select_14_routes_data_i14: assert property (
        @(posedge clk) (select == 5'd14) |-> (data_o == data_i14)
    );

    // select 15 routes data_i15 to data_o.
    check_select_15_routes_data_i15: assert property (
        @(posedge clk) (select == 5'd15) |-> (data_o == data_i15)
    );

    // select 16 routes data_i16 to data_o.
    check_select_16_routes_data_i16: assert property (
        @(posedge clk) (select == 5'd16) |-> (data_o == data_i16)
    );

    // select 17 routes data_i17 to data_o.
    check_select_17_routes_data_i17: assert property (
        @(posedge clk) (select == 5'd17) |-> (data_o == data_i17)
    );

    // select 18 routes data_i18 to data_o.
    check_select_18_routes_data_i18: assert property (
        @(posedge clk) (select == 5'd18) |-> (data_o == data_i18)
    );

    // select 19 routes data_i19 to data_o.
    check_select_19_routes_data_i19: assert property (
        @(posedge clk) (select == 5'd19) |-> (data_o == data_i19)
    );

    // select 20 routes data_i20 to data_o.
    check_select_20_routes_data_i20: assert property (
        @(posedge clk) (select == 5'd20) |-> (data_o == data_i20)
    );

    // select 21 routes data_i21 to data_o.
    check_select_21_routes_data_i21: assert property (
        @(posedge clk) (select == 5'd21) |-> (data_o == data_i21)
    );

    // select 22 routes data_i22 to data_o.
    check_select_22_routes_data_i22: assert property (
        @(posedge clk) (select == 5'd22) |-> (data_o == data_i22)
    );

    // select 23 routes data_i23 to data_o.
    check_select_23_routes_data_i23: assert property (
        @(posedge clk) (select == 5'd23) |-> (data_o == data_i23)
    );

    // select 24 routes data_i24 to data_o.
    check_select_24_routes_data_i24: assert property (
        @(posedge clk) (select == 5'd24) |-> (data_o == data_i24)
    );

    // select 25 routes data_i25 to data_o.
    check_select_25_routes_data_i25: assert property (
        @(posedge clk) (select == 5'd25) |-> (data_o == data_i25)
    );

    // select 26 routes data_i26 to data_o.
    check_select_26_routes_data_i26: assert property (
        @(posedge clk) (select == 5'd26) |-> (data_o == data_i26)
    );

    // select 27 routes data_i27 to data_o.
    check_select_27_routes_data_i27: assert property (
        @(posedge clk) (select == 5'd27) |-> (data_o == data_i27)
    );

    // select 28 routes data_i28 to data_o.
    check_select_28_routes_data_i28: assert property (
        @(posedge clk) (select == 5'd28) |-> (data_o == data_i28)
    );

    // select 29 routes data_i29 to data_o.
    check_select_29_routes_data_i29: assert property (
        @(posedge clk) (select == 5'd29) |-> (data_o == data_i29)
    );

    // select 30 routes data_i30 to data_o.
    check_select_30_routes_data_i30: assert property (
        @(posedge clk) (select == 5'd30) |-> (data_o == data_i30)
    );

    // select 31 routes data_i31 to data_o.
    check_select_31_routes_data_i31: assert property (
        @(posedge clk) (select == 5'd31) |-> (data_o == data_i31)
    );

endmodule
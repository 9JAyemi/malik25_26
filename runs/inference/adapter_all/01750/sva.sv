module MUX16_sva (
    input logic [3:0]  select,
    input logic [7:0]  data_i00,
    input logic [7:0]  data_i01,
    input logic [7:0]  data_i02,
    input logic [7:0]  data_i03,
    input logic [7:0]  data_i04,
    input logic [7:0]  data_i05,
    input logic [7:0]  data_i06,
    input logic [7:0]  data_i07,
    input logic [7:0]  data_i08,
    input logic [7:0]  data_i09,
    input logic [7:0]  data_i10,
    input logic [7:0]  data_i11,
    input logic [7:0]  data_i12,
    input logic [7:0]  data_i13,
    input logic [7:0]  data_i14,
    input logic [7:0]  data_i15,
    input logic [7:0]  data_o
);

    // select 0000 routes data_i00 to data_o.
    check_select_0000_routes_data_i00: assert property (
        @($global_clock) (select == 4'b0000) |-> (data_o == data_i00)
    );

    // select 0001 routes data_i01 to data_o.
    check_select_0001_routes_data_i01: assert property (
        @($global_clock) (select == 4'b0001) |-> (data_o == data_i01)
    );

    // select 0010 routes data_i02 to data_o.
    check_select_0010_routes_data_i02: assert property (
        @($global_clock) (select == 4'b0010) |-> (data_o == data_i02)
    );

    // select 0011 routes data_i03 to data_o.
    check_select_0011_routes_data_i03: assert property (
        @($global_clock) (select == 4'b0011) |-> (data_o == data_i03)
    );

    // select 0100 routes data_i04 to data_o.
    check_select_0100_routes_data_i04: assert property (
        @($global_clock) (select == 4'b0100) |-> (data_o == data_i04)
    );

    // select 0101 routes data_i05 to data_o.
    check_select_0101_routes_data_i05: assert property (
        @($global_clock) (select == 4'b0101) |-> (data_o == data_i05)
    );

    // select 0110 routes data_i06 to data_o.
    check_select_0110_routes_data_i06: assert property (
        @($global_clock) (select == 4'b0110) |-> (data_o == data_i06)
    );

    // select 0111 routes data_i07 to data_o.
    check_select_0111_routes_data_i07: assert property (
        @($global_clock) (select == 4'b0111) |-> (data_o == data_i07)
    );

    // select 1000 routes data_i08 to data_o.
    check_select_1000_routes_data_i08: assert property (
        @($global_clock) (select == 4'b1000) |-> (data_o == data_i08)
    );

    // select 1001 routes data_i09 to data_o.
    check_select_1001_routes_data_i09: assert property (
        @($global_clock) (select == 4'b1001) |-> (data_o == data_i09)
    );

    // select 1010 routes data_i10 to data_o.
    check_select_1010_routes_data_i10: assert property (
        @($global_clock) (select == 4'b1010) |-> (data_o == data_i10)
    );

    // select 1011 routes data_i11 to data_o.
    check_select_1011_routes_data_i11: assert property (
        @($global_clock) (select == 4'b1011) |-> (data_o == data_i11)
    );

    // select 1100 routes data_i12 to data_o.
    check_select_1100_routes_data_i12: assert property (
        @($global_clock) (select == 4'b1100) |-> (data_o == data_i12)
    );

    // select 1101 routes data_i13 to data_o.
    check_select_1101_routes_data_i13: assert property (
        @($global_clock) (select == 4'b1101) |-> (data_o == data_i13)
    );

    // select 1110 routes data_i14 to data_o.
    check_select_1110_routes_data_i14: assert property (
        @($global_clock) (select == 4'b1110) |-> (data_o == data_i14)
    );

    // select 1111 routes data_i15 to data_o.
    check_select_1111_routes_data_i15: assert property (
        @($global_clock) (select == 4'b1111) |-> (data_o == data_i15)
    );

endmodule
module MUX16_sva (
    // External sampling clock/reset (RTL has no clock/reset)
    input logic CLK,
    input logic RESETn, // active-low sampling reset for assertions
    // DUT ports
    input logic [3:0] select,
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
    input logic [7:0] data_o
);
    // Combinational 16:1 mux: data_o equals the selected input.

    // When select==0, output equals data_i00.
    check_mux_sel_0: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h0) |-> (data_o == data_i00)
    );

    // When select==1, output equals data_i01.
    check_mux_sel_1: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h1) |-> (data_o == data_i01)
    );

    // When select==2, output equals data_i02.
    check_mux_sel_2: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h2) |-> (data_o == data_i02)
    );

    // When select==3, output equals data_i03.
    check_mux_sel_3: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h3) |-> (data_o == data_i03)
    );

    // When select==4, output equals data_i04.
    check_mux_sel_4: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h4) |-> (data_o == data_i04)
    );

    // When select==5, output equals data_i05.
    check_mux_sel_5: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h5) |-> (data_o == data_i05)
    );

    // When select==6, output equals data_i06.
    check_mux_sel_6: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h6) |-> (data_o == data_i06)
    );

    // When select==7, output equals data_i07.
    check_mux_sel_7: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h7) |-> (data_o == data_i07)
    );

    // When select==8, output equals data_i08.
    check_mux_sel_8: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h8) |-> (data_o == data_i08)
    );

    // When select==9, output equals data_i09.
    check_mux_sel_9: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'h9) |-> (data_o == data_i09)
    );

    // When select==10, output equals data_i10.
    check_mux_sel_10: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'hA) |-> (data_o == data_i10)
    );

    // When select==11, output equals data_i11.
    check_mux_sel_11: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'hB) |-> (data_o == data_i11)
    );

    // When select==12, output equals data_i12.
    check_mux_sel_12: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'hC) |-> (data_o == data_i12)
    );

    // When select==13, output equals data_i13.
    check_mux_sel_13: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'hD) |-> (data_o == data_i13)
    );

    // When select==14, output equals data_i14.
    check_mux_sel_14: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'hE) |-> (data_o == data_i14)
    );

    // When select==15, output equals data_i15.
    check_mux_sel_15: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 4'hF) |-> (data_o == data_i15)
    );

endmodule
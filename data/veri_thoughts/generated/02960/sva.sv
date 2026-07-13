module top_module_sva (
    input logic [3:0] data1,
    input logic rotate,
    input logic [3:0] data2,
    input logic [1:0] select,
    input logic [3:0] out
);
    // When select==01, mux forwards data2 to out.
    check_mux_sel01_forwards_data2: assert property (
        @(posedge select[0]) (select == 2'b01) |-> (out == data2)
    );

    // When select==10, mux drives all zeros.
    check_mux_sel10_drives_zero: assert property (
        @(posedge select[0]) (select == 2'b10) |-> (out == 4'b0000)
    );

    // When select==11, mux drives 0001.
    check_mux_sel11_drives_one: assert property (
        @(posedge select[0]) (select == 2'b11) |-> (out == 4'b0001)
    );

    // When select==00 and no rotate, pass data1 through.
    check_sel00_no_rotate_passthrough: assert property (
        @(posedge select[0]) (select == 2'b00 && !rotate) |-> (out == data1)
    );

    // When select==00 and rotate, bit0 comes from data1[3].
    check_sel00_rotate_bit0: assert property (
        @(posedge select[0]) (select == 2'b00 && rotate) |-> (out[0] == data1[3])
    );

    // When select==00 and rotate, bit1 comes from data1[0].
    check_sel00_rotate_bit1: assert property (
        @(posedge select[0]) (select == 2'b00 && rotate) |-> (out[1] == data1[0])
    );

    // When select==00 and rotate, bit2 comes from data1[1].
    check_sel00_rotate_bit2: assert property (
        @(posedge select[0]) (select == 2'b00 && rotate) |-> (out[2] == data1[1])
    );

    // When select==00 and rotate, bit3 comes from data1[2].
    check_sel00_rotate_bit3: assert property (
        @(posedge select[0]) (select == 2'b00 && rotate) |-> (out[3] == data1[2])
    );
endmodule
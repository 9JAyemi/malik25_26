module mux4x1_sva (
    input logic clk,
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic [15:0] data2,
    input logic [15:0] data3,
    input logic [1:0] selectinput,
    input logic [15:0] out
);
    // Out equals the RTL's ternary mux function.
    check_mux_functional_equivalence: assert property (
        @(posedge clk) out == (selectinput[1] ? (selectinput[0] ? data3 : data2) : (selectinput[0] ? data1 : data0))
    );

    // When select is 00, out == data0.
    check_select_00_map: assert property (
        @(posedge clk) (selectinput == 2'b00) |-> (out == data0)
    );

    // When select is 01, out == data1.
    check_select_01_map: assert property (
        @(posedge clk) (selectinput == 2'b01) |-> (out == data1)
    );

    // When select is 10, out == data2.
    check_select_10_map: assert property (
        @(posedge clk) (selectinput == 2'b10) |-> (out == data2)
    );

    // When select is 11, out == data3.
    check_select_11_map: assert property (
        @(posedge clk) (selectinput == 2'b11) |-> (out == data3)
    );

    // If MSB is 0, out selects between data0/data1 by LSB.
    check_msb0_submux: assert property (
        @(posedge clk) (!selectinput[1]) |-> (out == (selectinput[0] ? data1 : data0))
    );

    // If MSB is 1, out selects between data2/data3 by LSB.
    check_msb1_submux: assert property (
        @(posedge clk) (selectinput[1]) |-> (out == (selectinput[0] ? data3 : data2))
    );

    // If LSB is 0, out selects between data0/data2 by MSB.
    check_lsb0_submux: assert property (
        @(posedge clk) (!selectinput[0]) |-> (out == (selectinput[1] ? data2 : data0))
    );

    // If LSB is 1, out selects between data1/data3 by MSB.
    check_lsb1_submux: assert property (
        @(posedge clk) (selectinput[0]) |-> (out == (selectinput[1] ? data3 : data1))
    );

    // Out changes only if select changes or the previously selected data input changes.
    check_out_change_causality: assert property (
        @(posedge clk)
        (out != $past(out)) |-> (
               (selectinput != $past(selectinput))
            || (($past(selectinput) == 2'b00) && (data0 != $past(data0)))
            || (($past(selectinput) == 2'b01) && (data1 != $past(data1)))
            || (($past(selectinput) == 2'b10) && (data2 != $past(data2)))
            || (($past(selectinput) == 2'b11) && (data3 != $past(data3)))
        )
    );
endmodule
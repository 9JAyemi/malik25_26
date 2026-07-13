module mux4to1_sva (
    input logic [3:0] data0x,
    input logic [3:0] data1x,
    input logic [3:0] data2x,
    input logic [3:0] data3x,
    input logic [1:0] sel,
    input logic [3:0] result
);
    default clocking cb @($global_clock); endclocking

    // When sel==00, result reflects data0x.
    select_data0_when_sel_00: assert property (
        (sel == 2'b00) |-> (result == data0x)
    );

    // When sel==01, result reflects data1x.
    select_data1_when_sel_01: assert property (
        (sel == 2'b01) |-> (result == data1x)
    );

    // When sel==10, result reflects data2x.
    select_data2_when_sel_10: assert property (
        (sel == 2'b10) |-> (result == data2x)
    );

    // When sel==11, result reflects data3x.
    select_data3_when_sel_11: assert property (
        (sel == 2'b11) |-> (result == data3x)
    );

    // Result equals the ternary-mux expression for all sel values.
    check_mux_function: assert property (
        result == ((sel == 2'b00) ? data0x :
                   (sel == 2'b01) ? data1x :
                   (sel == 2'b10) ? data2x :
                                    data3x)
    );

    // Result always matches one of the four data inputs.
    check_result_matches_some_input: assert property (
        (result == data0x) || (result == data1x) || (result == data2x) || (result == data3x)
    );
endmodule
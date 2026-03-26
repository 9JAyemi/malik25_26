module Multiplexer4_sva #(
    parameter int width = 1
) (
    input logic                   clk,
    input logic [width-1:0]       i_data0,
    input logic [width-1:0]       i_data1,
    input logic [width-1:0]       i_data2,
    input logic [width-1:0]       i_data3,
    input logic                   i_select0,
    input logic                   i_select1,
    input logic                   i_select2,
    input logic                   i_select3,
    input logic [width-1:0]       o_data,
    input logic                   o_error
);

    // Select0 has highest priority on o_data.
    check_select0_priority: assert property (
        @(posedge clk) i_select0 |-> (o_data == i_data0)
    );

    // Select1 drives o_data when select0 is low.
    check_select1_priority: assert property (
        @(posedge clk) (!i_select0 && i_select1) |-> (o_data == i_data1)
    );

    // Select2 drives o_data when higher-priority selects are low.
    check_select2_priority: assert property (
        @(posedge clk) (!i_select0 && !i_select1 && i_select2) |-> (o_data == i_data2)
    );

    // Select3 drives o_data when all higher-priority selects are low.
    check_select3_priority: assert property (
        @(posedge clk) (!i_select0 && !i_select1 && !i_select2 && i_select3) |-> (o_data == i_data3)
    );

    // No active select drives zero on o_data.
    check_no_select_data_zero: assert property (
        @(posedge clk) (!i_select0 && !i_select1 && !i_select2 && !i_select3) |-> (o_data == {width{1'b0}})
    );

    // o_data matches the implemented priority mux function.
    check_o_data_function: assert property (
        @(posedge clk)
        o_data == (i_select0 ? i_data0 :
                   i_select1 ? i_data1 :
                   i_select2 ? i_data2 :
                   i_select3 ? i_data3 : {width{1'b0}})
    );

    // No active select asserts o_error.
    check_no_select_error: assert property (
        @(posedge clk) (!i_select0 && !i_select1 && !i_select2 && !i_select3) |-> o_error
    );

    // Exactly one active select clears o_error.
    check_onehot_select_no_error: assert property (
        @(posedge clk)
        (( i_select0 && !i_select1 && !i_select2 && !i_select3) ||
         (!i_select0 &&  i_select1 && !i_select2 && !i_select3) ||
         (!i_select0 && !i_select1 &&  i_select2 && !i_select3) ||
         (!i_select0 && !i_select1 && !i_select2 &&  i_select3)) |-> !o_error
    );

    // Two or more active selects assert o_error.
    check_multiple_selects_error: assert property (
        @(posedge clk)
        ((i_select0 && i_select1) ||
         (i_select0 && i_select2) ||
         (i_select0 && i_select3) ||
         (i_select1 && i_select2) ||
         (i_select1 && i_select3) ||
         (i_select2 && i_select3)) |-> o_error
    );

    // o_error matches the implemented select-count behavior.
    check_o_error_function: assert property (
        @(posedge clk)
        o_error == ((!i_select0 && !i_select1 && !i_select2 && !i_select3) ||
                    (i_select0 && i_select1) ||
                    (i_select0 && i_select2) ||
                    (i_select0 && i_select3) ||
                    (i_select1 && i_select2) ||
                    (i_select1 && i_select3) ||
                    (i_select2 && i_select3))
    );

endmodule
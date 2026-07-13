module mux_3to4_sva (
    input logic       clk,
    input logic [2:0] data_in,
    input logic       enable,
    input logic [1:0] select,
    input logic [3:0] data_out
);

    // Output matches the RTL mux function for all input combinations.
    check_functional_mapping: assert property (
        @(posedge clk)
        data_out ==
        (enable
            ? ((select == 2'b00) ? {data_in[0], 1'b0, 1'b0, 1'b0} :
               (select == 2'b01) ? {1'b0, data_in[1], 1'b0, 1'b0} :
               (select == 2'b10) ? {1'b0, 1'b0, data_in[2], 1'b0} :
                                   4'b0000)
            : 4'b0000)
    );

    // When disabled, all outputs are low.
    check_disabled_forces_zero: assert property (
        @(posedge clk)
        !enable |-> (data_out == 4'b0000)
    );

    // Select 00 routes only data_in[0] to data_out[3].
    check_select_00_route: assert property (
        @(posedge clk)
        enable && (select == 2'b00) |-> (data_out == {data_in[0], 1'b0, 1'b0, 1'b0})
    );

    // Select 01 routes only data_in[1] to data_out[2].
    check_select_01_route: assert property (
        @(posedge clk)
        enable && (select == 2'b01) |-> (data_out == {1'b0, data_in[1], 1'b0, 1'b0})
    );

    // Select 10 routes only data_in[2] to data_out[1].
    check_select_10_route: assert property (
        @(posedge clk)
        enable && (select == 2'b10) |-> (data_out == {1'b0, 1'b0, data_in[2], 1'b0})
    );

    // Select 11 forces all outputs low.
    check_select_11_zero: assert property (
        @(posedge clk)
        enable && (select == 2'b11) |-> (data_out == 4'b0000)
    );

    // The least significant output bit is always zero.
    check_lsb_always_zero: assert property (
        @(posedge clk)
        data_out[0] == 1'b0
    );

    // The output is always zero or a single active routed bit.
    check_legal_output_patterns: assert property (
        @(posedge clk)
        (data_out == 4'b0000) || (data_out == 4'b1000) || (data_out == 4'b0100) || (data_out == 4'b0010)
    );

    // data_out[3] can only be high for select 00 with data_in[0] high.
    check_bit3_source_condition: assert property (
        @(posedge clk)
        data_out[3] |-> enable && (select == 2'b00) && data_in[0]
    );

    // data_out[2] can only be high for select 01 with data_in[1] high.
    check_bit2_source_condition: assert property (
        @(posedge clk)
        data_out[2] |-> enable && (select == 2'b01) && data_in[1]
    );

    // data_out[1] can only be high for select 10 with data_in[2] high.
    check_bit1_source_condition: assert property (
        @(posedge clk)
        data_out[1] |-> enable && (select == 2'b10) && data_in[2]
    );

endmodule
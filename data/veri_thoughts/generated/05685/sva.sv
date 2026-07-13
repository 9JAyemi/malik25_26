module mux_or_sva (
    input logic       clk,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic       select,
    input logic [3:0] out
);

    // Output matches the composed mux-and-OR function.
    check_full_function: assert property (
        @(posedge clk) out == ((select ? data1 : data0) | (select ? data3 : data2))
    );

    // Low select chooses data0 and data2.
    check_select_low_function: assert property (
        @(posedge clk) !select |-> (out == (data0 | data2))
    );

    // High select chooses data1 and data3.
    check_select_high_function: assert property (
        @(posedge clk) select |-> (out == (data1 | data3))
    );

    // Bit 0 matches the selected inputs after the OR.
    check_bit0_function: assert property (
        @(posedge clk) out[0] == ((select ? data1[0] : data0[0]) | (select ? data3[0] : data2[0]))
    );

    // Bit 1 matches the selected inputs after the OR.
    check_bit1_function: assert property (
        @(posedge clk) out[1] == ((select ? data1[1] : data0[1]) | (select ? data3[1] : data2[1]))
    );

    // Bit 2 matches the selected inputs after the OR.
    check_bit2_function: assert property (
        @(posedge clk) out[2] == ((select ? data1[2] : data0[2]) | (select ? data3[2] : data2[2]))
    );

    // Bit 3 matches the selected inputs after the OR.
    check_bit3_function: assert property (
        @(posedge clk) out[3] == ((select ? data1[3] : data0[3]) | (select ? data3[3] : data2[3]))
    );

    // Stable inputs and select keep the output stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({data0, data1, data2, data3, select}) |-> $stable(out)
    );

    // With low select held stable, data1 and data3 do not affect out.
    check_low_select_ignores_unselected_inputs: assert property (
        @(posedge clk) ($stable(select) && !select && $stable({data0, data2})) |-> $stable(out)
    );

    // With high select held stable, data0 and data2 do not affect out.
    check_high_select_ignores_unselected_inputs: assert property (
        @(posedge clk) ($stable(select) && select && $stable({data1, data3})) |-> $stable(out)
    );

endmodule
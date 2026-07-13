module mux_adder_assertions (
    input logic [2:0] sel_mux1,
    input logic [2:0] sel_mux2,
    input logic [3:0] data0_mux1,
    input logic [3:0] data1_mux1,
    input logic [3:0] data2_mux1,
    input logic [3:0] data3_mux1,
    input logic [3:0] data4_mux1,
    input logic [3:0] data5_mux1,
    input logic [3:0] data0_mux2,
    input logic [3:0] data1_mux2,
    input logic [3:0] data2_mux2,
    input logic [3:0] data3_mux2,
    input logic [3:0] data4_mux2,
    input logic [3:0] data5_mux2,
    input logic       sel_mux,
    input logic [3:0] out
);

    function automatic logic [3:0] selected_data (
        input logic [2:0] sel,
        input logic [3:0] d0,
        input logic [3:0] d1,
        input logic [3:0] d2,
        input logic [3:0] d3,
        input logic [3:0] d4,
        input logic [3:0] d5
    );
    begin
        case (sel)
            3'b000: selected_data = d0;
            3'b001: selected_data = d1;
            3'b010: selected_data = d2;
            3'b011: selected_data = d3;
            3'b100: selected_data = d4;
            3'b101: selected_data = d5;
            default: selected_data = 4'b0000;
        endcase
    end
    endfunction

    function automatic logic selector_invalid (
        input logic [2:0] sel
    );
    begin
        selector_invalid = (sel == 3'b110) || (sel == 3'b111);
    end
    endfunction

    // Output must equal the sum of the two mux-selected values.
    check_out_matches_selected_sum: assert property (
        @($global_clock)
        out == (
            selected_data(sel_mux1, data0_mux1, data1_mux1, data2_mux1, data3_mux1, data4_mux1, data5_mux1) +
            selected_data(sel_mux2, data0_mux2, data1_mux2, data2_mux2, data3_mux2, data4_mux2, data5_mux2)
        )
    );

    // With mux2 defaulted to zero, sel_mux1=000 must pass data0_mux1.
    check_mux1_select_data0: assert property (
        @($global_clock)
        (sel_mux1 == 3'b000 && selector_invalid(sel_mux2)) |-> (out == data0_mux1)
    );

    // With mux2 defaulted to zero, sel_mux1=001 must pass data1_mux1.
    check_mux1_select_data1: assert property (
        @($global_clock)
        (sel_mux1 == 3'b001 && selector_invalid(sel_mux2)) |-> (out == data1_mux1)
    );

    // With mux2 defaulted to zero, sel_mux1=010 must pass data2_mux1.
    check_mux1_select_data2: assert property (
        @($global_clock)
        (sel_mux1 == 3'b010 && selector_invalid(sel_mux2)) |-> (out == data2_mux1)
    );

    // With mux2 defaulted to zero, sel_mux1=011 must pass data3_mux1.
    check_mux1_select_data3: assert property (
        @($global_clock)
        (sel_mux1 == 3'b011 && selector_invalid(sel_mux2)) |-> (out == data3_mux1)
    );

    // With mux2 defaulted to zero, sel_mux1=100 must pass data4_mux1.
    check_mux1_select_data4: assert property (
        @($global_clock)
        (sel_mux1 == 3'b100 && selector_invalid(sel_mux2)) |-> (out == data4_mux1)
    );

    // With mux2 defaulted to zero, sel_mux1=101 must pass data5_mux1.
    check_mux1_select_data5: assert property (
        @($global_clock)
        (sel_mux1 == 3'b101 && selector_invalid(sel_mux2)) |-> (out == data5_mux1)
    );

    // With mux1 defaulted to zero, sel_mux2=000 must pass data0_mux2.
    check_mux2_select_data0: assert property (
        @($global_clock)
        (selector_invalid(sel_mux1) && sel_mux2 == 3'b000) |-> (out == data0_mux2)
    );

    // With mux1 defaulted to zero, sel_mux2=001 must pass data1_mux2.
    check_mux2_select_data1: assert property (
        @($global_clock)
        (selector_invalid(sel_mux1) && sel_mux2 == 3'b001) |-> (out == data1_mux2)
    );

    // With mux1 defaulted to zero, sel_mux2=010 must pass data2_mux2.
    check_mux2_select_data2: assert property (
        @($global_clock)
        (selector_invalid(sel_mux1) && sel_mux2 == 3'b010) |-> (out == data2_mux2)
    );

    // With mux1 defaulted to zero, sel_mux2=011 must pass data3_mux2.
    check_mux2_select_data3: assert property (
        @($global_clock)
        (selector_invalid(sel_mux1) && sel_mux2 == 3'b011) |-> (out == data3_mux2)
    );

    // With mux1 defaulted to zero, sel_mux2=100 must pass data4_mux2.
    check_mux2_select_data4: assert property (
        @($global_clock)
        (selector_invalid(sel_mux1) && sel_mux2 == 3'b100) |-> (out == data4_mux2)
    );

    // With mux1 defaulted to zero, sel_mux2=101 must pass data5_mux2.
    check_mux2_select_data5: assert property (
        @($global_clock)
        (selector_invalid(sel_mux1) && sel_mux2 == 3'b101) |-> (out == data5_mux2)
    );

    // Changing sel_mux alone must not affect out because it is not used in the output logic.
    check_sel_mux_has_no_effect_on_out: assert property (
        @($global_clock)
        $changed(sel_mux) &&
        $stable({
            sel_mux1, sel_mux2,
            data0_mux1, data1_mux1, data2_mux1, data3_mux1, data4_mux1, data5_mux1,
            data0_mux2, data1_mux2, data2_mux2, data3_mux2, data4_mux2, data5_mux2
        }) |-> $stable(out)
    );

endmodule
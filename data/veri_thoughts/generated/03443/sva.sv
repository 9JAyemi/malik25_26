module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic [1:0] select,
    input logic out_assign,
    input logic out_alwaysblock,
    input logic final_output
);

    // out_alwaysblock must match the three-input OR.
    check_or_output: assert property (
        @($global_clock) out_alwaysblock == (a | b | c)
    );

    // out_assign is the mux LSB, which is 0 for select 00.
    check_out_assign_sel_00: assert property (
        @($global_clock) (select == 2'b00) |-> (out_assign == 1'b0)
    );

    // out_assign is the mux LSB, which equals b for select 01.
    check_out_assign_sel_01: assert property (
        @($global_clock) (select == 2'b01) |-> (out_assign == b)
    );

    // out_assign is the mux LSB, which equals c for select 10.
    check_out_assign_sel_10: assert property (
        @($global_clock) (select == 2'b10) |-> (out_assign == c)
    );

    // out_assign is the mux LSB, which is 0 for select 11.
    check_out_assign_sel_11: assert property (
        @($global_clock) (select == 2'b11) |-> (out_assign == 1'b0)
    );

    // final_output selects out_assign on select[0], else out_alwaysblock.
    check_final_output_select: assert property (
        @($global_clock) final_output == (select[0] ? out_assign : out_alwaysblock)
    );

endmodule
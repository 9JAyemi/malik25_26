module mux12_v10_sva (
    input  logic        CLK,
    input  logic [11:0] I,
    input  logic [1:0]  select,
    input  logic        O
);
    // O equals the final case mapping (I[8..11] selected by select).
    check_func_equiv_to_last_case: assert property (
        @(posedge CLK) O == (select == 2'b00 ? I[8] :
                             select == 2'b01 ? I[9] :
                             select == 2'b10 ? I[10] : I[11])
    );

    // When select==00, O equals I[8].
    check_map_sel_00: assert property (
        @(posedge CLK) (select == 2'b00) |-> (O == I[8])
    );
    // When select==01, O equals I[9].
    check_map_sel_01: assert property (
        @(posedge CLK) (select == 2'b01) |-> (O == I[9])
    );
    // When select==10, O equals I[10].
    check_map_sel_10: assert property (
        @(posedge CLK) (select == 2'b10) |-> (O == I[10])
    );
    // When select==11, O equals I[11].
    check_map_sel_11: assert property (
        @(posedge CLK) (select == 2'b11) |-> (O == I[11])
    );

    // If select and I[8..11] are stable, O must be stable.
    check_stable_when_relevant_stable: assert property (
        @(posedge CLK) (!$initstate && $stable(select) && $stable(I[8]) && $stable(I[9]) && $stable(I[10]) && $stable(I[11]))
                       |-> $stable(O)
    );

    // If O changes, then select or one of I[8..11] changed.
    check_output_change_has_cause: assert property (
        @(posedge CLK) (!$initstate && !$stable(O))
                       |-> (!$stable(select) || !$stable(I[8]) || !$stable(I[9]) || !$stable(I[10]) || !$stable(I[11]))
    );

    // With select stable at 00, O changes when I[8] changes.
    check_follow_sel00_input_changes: assert property (
        @(posedge CLK) (!$initstate && $stable(select) && (select == 2'b00) && !$stable(I[8]))
                       |-> (!$stable(O))
    );
    // With select stable at 01, O changes when I[9] changes.
    check_follow_sel01_input_changes: assert property (
        @(posedge CLK) (!$initstate && $stable(select) && (select == 2'b01) && !$stable(I[9]))
                       |-> (!$stable(O))
    );
    // With select stable at 10, O changes when I[10] changes.
    check_follow_sel10_input_changes: assert property (
        @(posedge CLK) (!$initstate && $stable(select) && (select == 2'b10) && !$stable(I[10]))
                       |-> (!$stable(O))
    );
    // With select stable at 11, O changes when I[11] changes.
    check_follow_sel11_input_changes: assert property (
        @(posedge CLK) (!$initstate && $stable(select) && (select == 2'b11) && !$stable(I[11]))
                       |-> (!$stable(O))
    );
endmodule
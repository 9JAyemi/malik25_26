module mux_4to1_structural_sva (
    input logic [3:0] data_in,
    input logic [1:0] select,
    input logic data_out,
    input logic and1,
    input logic and2,
    input logic and3,
    input logic and4,
    input logic or1,
    input logic or2
);

    // No RTL clock or reset is present; sample combinational behavior on $global_clock.

    // and1 passes data_in[0] only for select 00.
    check_and1_gate: assert property (
        @($global_clock) and1 === ((select == 2'b00) ? data_in[0] : 1'b0)
    );

    // and2 passes data_in[1] only for select 01.
    check_and2_gate: assert property (
        @($global_clock) and2 === ((select == 2'b01) ? data_in[1] : 1'b0)
    );

    // and3 passes data_in[2] only for select 10.
    check_and3_gate: assert property (
        @($global_clock) and3 === ((select == 2'b10) ? data_in[2] : 1'b0)
    );

    // and4 passes data_in[3] only for select 11.
    check_and4_gate: assert property (
        @($global_clock) and4 === ((select == 2'b11) ? data_in[3] : 1'b0)
    );

    // or1 is the OR of and1 and and2.
    check_or1_combine: assert property (
        @($global_clock) or1 === (and1 | and2)
    );

    // or2 is the OR of and3 and and4.
    check_or2_combine: assert property (
        @($global_clock) or2 === (and3 | and4)
    );

    // Select 00 forwards data_in[0] to data_out.
    check_select_00_output: assert property (
        @($global_clock) (select === 2'b00) |-> (data_out === data_in[0])
    );

    // Select 01 forwards data_in[1] to data_out.
    check_select_01_output: assert property (
        @($global_clock) (select === 2'b01) |-> (data_out === data_in[1])
    );

    // Select 10 forwards data_in[2] to data_out.
    check_select_10_output: assert property (
        @($global_clock) (select === 2'b10) |-> (data_out === data_in[2])
    );

    // Select 11 forwards data_in[3] to data_out.
    check_select_11_output: assert property (
        @($global_clock) (select === 2'b11) |-> (data_out === data_in[3])
    );

endmodule
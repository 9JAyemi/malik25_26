module shift_mux_assertions (
    input logic [3:0] data_in,
    input logic [3:0] in_0,
    input logic [3:0] in_1,
    input logic [3:0] in_2,
    input logic [3:0] in_3,
    input logic [1:0] sel,
    input logic shift,
    input logic [3:0] out,
    input logic [3:0] shift_reg
);

    // shift_reg upper bits shift from the previous lower bits.
    check_shift_reg_shift: assert property (
        @(posedge shift) 1'b1 |=> (shift_reg[3:1] === $past(shift_reg[2:0]))
    );

    // shift_reg loads data_in[3] into bit 0 on each shift edge.
    check_shift_reg_load_bit3: assert property (
        @(posedge shift) 1'b1 |=> (shift_reg[0] === $past(data_in[3]))
    );

    // out selects in_0 when sel is 2'b00.
    check_out_sel_00: assert property (
        @(posedge shift) (sel === 2'b00) |-> (out === in_0)
    );

    // out selects in_1 when sel is 2'b01.
    check_out_sel_01: assert property (
        @(posedge shift) (sel === 2'b01) |-> (out === in_1)
    );

    // out selects in_2 when sel is 2'b10.
    check_out_sel_10: assert property (
        @(posedge shift) (sel === 2'b10) |-> (out === in_2)
    );

    // out selects in_3 when sel is 2'b11.
    check_out_sel_11: assert property (
        @(posedge shift) (sel === 2'b11) |-> (out === in_3)
    );

    // out stays stable when sel and all mux inputs stay stable.
    check_out_stable_when_mux_inputs_stable: assert property (
        @(posedge shift)
        1'b1 |=> (
            !((sel  === $past(sel))  &&
              (in_0 === $past(in_0)) &&
              (in_1 === $past(in_1)) &&
              (in_2 === $past(in_2)) &&
              (in_3 === $past(in_3))) ||
            (out === $past(out))
        )
    );

endmodule
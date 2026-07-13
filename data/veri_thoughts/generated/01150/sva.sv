module shift_register_sva (
    input logic [3:0] DATA_IN,
    input logic       LOAD,
    input logic       CLK,
    input logic [3:0] DATA_OUT
);

    // Next-state equals load (prev) or rotate-left-1 (prev) of DATA_OUT.
    check_next_state_rule: assert property (
        @(posedge CLK)
            DATA_OUT == ( $past(LOAD)
                          ? $past(DATA_IN)
                          : { $past(DATA_OUT[2:0]), $past(DATA_OUT[3]) } )
    );

    // If LOAD was 1 in the previous cycle, DATA_OUT captures previous DATA_IN.
    check_load_captures_data: assert property (
        @(posedge CLK)
            $past(LOAD) |-> (DATA_OUT == $past(DATA_IN))
    );

    // If LOAD was 0 in the previous cycle, DATA_OUT rotates left by 1.
    check_rotate_when_no_load: assert property (
        @(posedge CLK)
            $past(!LOAD) |-> (DATA_OUT == { $past(DATA_OUT[2:0]), $past(DATA_OUT[3]) })
    );

    // Rotate mapping for bit3 when not loading: new[3] = old[2].
    check_rotate_bit3: assert property (
        @(posedge CLK)
            $past(!LOAD) |-> (DATA_OUT[3] == $past(DATA_OUT[2]))
    );

    // Rotate mapping for bit2 when not loading: new[2] = old[1].
    check_rotate_bit2: assert property (
        @(posedge CLK)
            $past(!LOAD) |-> (DATA_OUT[2] == $past(DATA_OUT[1]))
    );

    // Rotate mapping for bit1 when not loading: new[1] = old[0].
    check_rotate_bit1: assert property (
        @(posedge CLK)
            $past(!LOAD) |-> (DATA_OUT[1] == $past(DATA_OUT[0]))
    );

    // Rotate mapping for bit0 when not loading: new[0] = old[3].
    check_rotate_bit0: assert property (
        @(posedge CLK)
            $past(!LOAD) |-> (DATA_OUT[0] == $past(DATA_OUT[3]))
    );

    // Four consecutive rotates (no LOAD for 4 cycles) return to the original value.
    check_four_rotate_identity: assert property (
        @(posedge CLK)
            $past(!LOAD,1) && $past(!LOAD,2) && $past(!LOAD,3) && $past(!LOAD,4)
            |-> (DATA_OUT == $past(DATA_OUT,4))
    );

endmodule
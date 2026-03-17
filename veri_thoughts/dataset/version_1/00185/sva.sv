module shift_register_sva (
    input logic       CLK,
    input logic       LOAD,
    input logic [3:0] DATA,
    input logic [3:0] Q
);

    // A load cycle captures DATA into Q by the next sampled clock.
    check_load_captures_data: assert property (
        @(posedge CLK) LOAD |=> (Q == $past(DATA))
    );

    // A non-load cycle shifts Q left and inserts 0 into bit 0.
    check_shift_behavior: assert property (
        @(posedge CLK) !LOAD |=> (Q == {$past(Q[2:0]), 1'b0})
    );

    // A non-load cycle always drives the next LSB low.
    check_shift_inserts_zero: assert property (
        @(posedge CLK) !LOAD |=> (Q[0] == 1'b0)
    );

    // A non-load cycle moves the prior lower bits into the upper bits.
    check_shift_moves_bits: assert property (
        @(posedge CLK) !LOAD |=> (Q[3:1] == $past(Q[2:0]))
    );

    // Four consecutive shift cycles clear the register.
    check_four_shifts_clear_register: assert property (
        @(posedge CLK) ((!LOAD)[*4]) |=> (Q == 4'b0000)
    );

endmodule
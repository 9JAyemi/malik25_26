module check_tuple_sva(
    input logic clk,
    input logic [2:0] tuple,
    input logic valid
);

    // Combinational DUT sampled on clk; the RTL has no reset.

    // valid must match the RTL expression exactly.
    check_valid_definition: assert property (
        @(posedge clk) disable iff (1'b0)
            valid == (((tuple[0] ^ tuple[1]) == tuple[2]) &&
                      ((tuple[1] ^ tuple[2]) == tuple[0]) &&
                      ((tuple[0] ^ tuple[2]) == tuple[1]))
    );

    // valid is high exactly for even-parity tuples.
    check_valid_even_parity: assert property (
        @(posedge clk) disable iff (1'b0)
            valid == (~^tuple)
    );

    // A high valid requires tuple[0] ^ tuple[1] to equal tuple[2].
    check_valid_implies_xor01_eq_2: assert property (
        @(posedge clk) disable iff (1'b0)
            valid |-> ((tuple[0] ^ tuple[1]) == tuple[2])
    );

    // A high valid requires tuple[1] ^ tuple[2] to equal tuple[0].
    check_valid_implies_xor12_eq_0: assert property (
        @(posedge clk) disable iff (1'b0)
            valid |-> ((tuple[1] ^ tuple[2]) == tuple[0])
    );

    // A high valid requires tuple[0] ^ tuple[2] to equal tuple[1].
    check_valid_implies_xor02_eq_1: assert property (
        @(posedge clk) disable iff (1'b0)
            valid |-> ((tuple[0] ^ tuple[2]) == tuple[1])
    );

    // tuple[0] ^ tuple[1] matching tuple[2] is sufficient for valid.
    check_xor01_eq_2_implies_valid: assert property (
        @(posedge clk) disable iff (1'b0)
            ((tuple[0] ^ tuple[1]) == tuple[2]) |-> valid
    );

    // tuple[1] ^ tuple[2] matching tuple[0] is sufficient for valid.
    check_xor12_eq_0_implies_valid: assert property (
        @(posedge clk) disable iff (1'b0)
            ((tuple[1] ^ tuple[2]) == tuple[0]) |-> valid
    );

    // tuple[0] ^ tuple[2] matching tuple[1] is sufficient for valid.
    check_xor02_eq_1_implies_valid: assert property (
        @(posedge clk) disable iff (1'b0)
            ((tuple[0] ^ tuple[2]) == tuple[1]) |-> valid
    );

endmodule
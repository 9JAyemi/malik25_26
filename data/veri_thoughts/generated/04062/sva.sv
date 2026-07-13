module shift_register_sva (
    input logic [7:0] in,
    input logic       shift,
    input logic       reset,
    input logic       clk,
    input logic [7:0] out
);

    // When reset is asserted, the output is cleared to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 8'b0)
    );

    // When shift is asserted, the next output value matches the input bus.
    check_shift_updates_out_from_in: assert property (
        @(posedge clk) disable iff (reset)
        shift |=> (out == $past(in))
    );

    // When shift is deasserted, the output holds its previous value.
    check_no_shift_holds_out: assert property (
        @(posedge clk) disable iff (reset)
        !shift |=> (out == $past(out))
    );

endmodule
module FFType_sva (
    input logic clock,
    input logic reset,
    input logic io_in,
    input logic io_init,
    input logic io_out,
    input logic io_enable
);

    // Reset forces the output to the initialized value.
    check_reset_forces_init: assert property (
        @(posedge clock) reset |=> (io_out == $past(io_init))
    );

    // With enable low, the output holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clock) disable iff (reset)
        !io_enable |=> (io_out == $past(io_out))
    );

    // With enable high, the output captures io_in.
    check_capture_when_enabled: assert property (
        @(posedge clock) disable iff (reset)
        io_enable |=> (io_out == $past(io_in))
    );

endmodule
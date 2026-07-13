module soft_clock_sva
#(
    parameter C_SIPIF_DWIDTH = 32
)
(
    input  logic                              Bus2IP_Reset,
    input  logic                              Bus2IP_Clk,
    input  logic                              Bus2IP_WrCE,
    input  logic [0:C_SIPIF_DWIDTH-1]         Bus2IP_Data,
    input  logic [0:(C_SIPIF_DWIDTH/8)-1]     Bus2IP_BE,
    input  logic                              Clk2IP_Clk,
    input  logic                              Clk2Bus_WrAck,
    input  logic                              Clk2Bus_Error,
    input  logic                              Clk2Bus_ToutSup
);

    localparam [0:3] CLOCK_ENABLE  = 4'b1010;
    localparam [0:3] CLOCK_DISABLE = 4'b0101;

    wire isc_enable_match  = (Bus2IP_Data[C_SIPIF_DWIDTH-4:C_SIPIF_DWIDTH-1] == CLOCK_ENABLE);
    wire isc_disable_match = (Bus2IP_Data[C_SIPIF_DWIDTH-4:C_SIPIF_DWIDTH-1] == CLOCK_DISABLE);
    wire isc_match         = isc_enable_match | isc_disable_match;
    wire isc_mismatch      = ~(isc_enable_match | isc_disable_match);
    wire isc_be_match      = (Bus2IP_BE[(C_SIPIF_DWIDTH/8)-1] == 1'b1);

    // Timeout support output is high whenever reset is asserted.
    check_toutsup_high_in_reset: assert property (
        @(posedge Bus2IP_Clk)
        Bus2IP_Reset |-> Clk2Bus_ToutSup
    );

    // Timeout support output is low whenever reset is deasserted.
    check_toutsup_low_out_of_reset: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        !Clk2Bus_ToutSup
    );

    // Write acknowledge matches the command and byte-enable decode.
    check_wrack_decode: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Clk2Bus_WrAck == (isc_match && Bus2IP_WrCE && isc_be_match))
    );

    // Error response matches the invalid-command and byte-enable decode.
    check_error_decode: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Clk2Bus_Error == (isc_mismatch && Bus2IP_WrCE && isc_be_match))
    );

    // Acknowledge and error are never asserted together.
    check_ack_error_mutex: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        !(Clk2Bus_WrAck && Clk2Bus_Error)
    );

    // A valid write with the selected byte enabled gets exactly one response.
    check_valid_be_write_has_one_response: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Bus2IP_WrCE && isc_be_match) |-> (Clk2Bus_WrAck ^ Clk2Bus_Error)
    );

    // Writes with the selected byte disabled produce no bus response.
    check_bad_be_write_has_no_response: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Bus2IP_WrCE && !isc_be_match) |-> (!Clk2Bus_WrAck && !Clk2Bus_Error)
    );

    // A valid disable command turns off the gated clock on the next cycle.
    check_disable_write_turns_off_clock_next_cycle: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Bus2IP_WrCE && isc_be_match && isc_disable_match) |=> !Clk2IP_Clk
    );

    // A valid enable command turns on the gated clock on the next cycle.
    check_enable_write_turns_on_clock_next_cycle: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Bus2IP_WrCE && isc_be_match && isc_enable_match) |=> Clk2IP_Clk
    );

    // Once on, the gated clock stays on unless a valid disable command is written.
    check_clock_holds_high_without_disable: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (Clk2IP_Clk && !(Bus2IP_WrCE && isc_be_match && isc_disable_match)) |=> Clk2IP_Clk
    );

    // Once off, the gated clock stays off unless a valid enable command is written.
    check_clock_holds_low_without_enable: assert property (
        @(posedge Bus2IP_Clk) disable iff (Bus2IP_Reset)
        (!Clk2IP_Clk && !(Bus2IP_WrCE && isc_be_match && isc_enable_match)) |=> !Clk2IP_Clk
    );

endmodule
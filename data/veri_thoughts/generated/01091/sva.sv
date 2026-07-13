module jaxa_errorStatus_sva (
    input logic        clk,
    input logic        reset_n,
    input logic [1:0]  address,
    input logic [7:0]  in_port,
    input logic [31:0] readdata
);

    ///// Reset behavior /////
    // During reset, readdata must be zero.
    check_reset_clears_readdata: assert property (
        @(posedge clk) (!reset_n) |-> (readdata == 32'h0)
    );

    ///// Structural invariants /////
    // Upper 24 bits are always zero when not in reset.
    check_upper_bytes_zero: assert property (
        @(posedge clk) disable iff (!reset_n) readdata[31:8] == 24'h0
    );

    ///// Registered update semantics /////
    // On each cycle out of reset, readdata equals zero-extended muxed data from the prior cycle.
    check_registered_output_matches_prev_cycle: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (readdata == {24'h0, ($past(address) == 2'b00) ? $past(in_port) : 8'h00})
    );

    // If previous address was 00, the low byte equals previous in_port.
    check_low_byte_tracks_in_port_when_addr0: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && ($past(address) == 2'b00) |-> (readdata[7:0] == $past(in_port))
    );

    // If previous address was not 00, the low byte is zero.
    check_low_byte_zero_when_addr_not0: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && ($past(address) != 2'b00) |-> (readdata[7:0] == 8'h00)
    );

endmodule
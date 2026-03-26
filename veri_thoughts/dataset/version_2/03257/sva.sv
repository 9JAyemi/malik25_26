module switch_sva (
    input logic [1:0]  address,
    input logic        clk,
    input logic [7:0]  in_port,
    input logic        reset_n,
    input logic [31:0] readdata
);

    // When reset is sampled low, readdata is cleared.
    check_reset_clears_readdata: assert property (
        @(posedge clk) (!$initstate && !reset_n) |-> (readdata == 32'h0000_0000)
    );

    // Address 0 causes the next registered read to return the input byte.
    check_address_zero_captures_input: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |=> (readdata == {24'h000000, $past(in_port)})
    );

    // Nonzero addresses cause the next registered read to return zero.
    check_nonzero_address_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |=> (readdata == 32'h0000_0000)
    );

    // Each active clock loads the muxed read value into readdata.
    check_registered_read_data: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (readdata == (($past(address) == 2'b00) ? {24'h000000, $past(in_port)} : 32'h0000_0000))
    );

    // The registered read value is always zero-extended on the next cycle.
    check_zero_extended_readdata: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (readdata[31:8] == 24'h000000)
    );

endmodule
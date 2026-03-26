module memory_interface_sva (
    input logic [1:0]  address,
    input logic        clk,
    input logic [10:0] in_port,
    input logic        reset_n,
    input logic [31:0] readdata
);

    // A clock edge with reset asserted clears readdata by the next sampled cycle.
    check_reset_clears_readdata: assert property (
        @(posedge clk)
        (!reset_n) |=> (readdata == 32'b0)
    );

    // Address 0 captures in_port into readdata on the following cycle.
    check_address_zero_captures_input: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |=> (readdata == {21'b0, $past(in_port)})
    );

    // Any nonzero address produces zero readdata on the following cycle.
    check_nonzero_address_reads_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |=> (readdata == 32'b0)
    );

    // Every non-reset update keeps the upper bits of readdata at zero.
    check_readdata_zero_extended: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (readdata[31:11] == 21'b0)
    );

endmodule
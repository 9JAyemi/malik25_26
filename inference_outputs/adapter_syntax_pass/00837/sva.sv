module wasca_hexdot_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [5:0]  out_port,
    input logic [31:0] readdata
);

    // Reset clears the stored output value.
    check_reset_clears_out_port: assert property (
        @(posedge clk) !reset_n |-> (out_port == 6'h00)
    );

    // Reset clears the readback data.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'h00000000)
    );

    // Address 0 reads back the stored output value.
    check_read_address_zero_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'h0) |-> (readdata == {26'b0, out_port})
    );

    // Nonzero addresses read zero.
    check_read_nonzero_address_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'h0) |-> (readdata == 32'h00000000)
    );

    // A selected write to address 0 updates the stored output value.
    check_write_address_zero_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'h0)) |=> (out_port == $past(writedata[5:0]))
    );

    // Without a selected write to address 0, the stored output value holds.
    check_no_write_address_zero_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n && (address == 2'h0)) |=> (out_port == $past(out_port))
    );

endmodule
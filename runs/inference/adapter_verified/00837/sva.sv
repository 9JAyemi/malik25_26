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

// Reset clears the readback value.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'h00000000)
    );

// Address 0 writes load the lower 6 bits of writedata into out_port.
    check_write_loads_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'h0)) |=> (out_port == $past(writedata[5:0]))
    );

// Nonzero addresses do not modify out_port.
    check_nonzero_address_ignored: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((address != 2'h0) || write_n || !chipselect) |=> (out_port == $past(out_port))
    );

// A write to address 0 with chipselect low does not modify out_port.
    check_chipselect_low_ignored: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect == 1'b0) |=> (out_port == $past(out_port))
    );

// A write to address 0 with write_n high does not modify out_port.
    check_write_n_high_ignored: assert property (
        @(posedge clk) disable iff (!reset_n)
        (write_n == 1'b1) |=> (out_port == $past(out_port))
    );

// Reads from address 0 return the current out_port value.
    check_read_address_0_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'h0) |-> (readdata == {26'b0, out_port})
    );

// Reads from nonzero addresses return zero.
    check_read_nonzero_address_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'h0) |-> (readdata == 32'h00000000)
    );

endmodule

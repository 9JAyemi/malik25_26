module soc_system_pio_aliveTest_cpu_s0_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [1:0]  out_port,
    input logic [31:0] readdata
);

    // Clock: clk; reset: reset_n active low; mixed sequential/combinational logic.

    // Reset forces the registered output low.
    reset_clears_out_port: assert property (
        @(posedge clk) !reset_n |-> (out_port == 2'b00)
    );

    // Reset forces the readback value low.
    reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'b0)
    );

    // Read data is always zero-extended in the upper 30 bits.
    read_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (readdata[31:2] == 30'b0)
    );

    // Address 0 returns the current output register value.
    read_addr_zero_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |-> (readdata == {30'b0, out_port})
    );

    // Nonzero addresses return zero.
    read_nonzero_addr_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |-> (readdata == 32'b0)
    );

    // A write to address 0 updates the output register with writedata[1:0].
    write_addr_zero_captures_low_bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata[1:0]))
    );

    // When not selected, the output register holds its value.
    unselected_cycle_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!chipselect) |=> (out_port == $past(out_port))
    );

    // Read cycles do not modify the output register.
    read_cycle_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && write_n) |=> (out_port == $past(out_port))
    );

    // Writes to nonzero addresses do not modify the output register.
    write_nonzero_addr_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address != 2'b00)) |=> (out_port == $past(out_port))
    );

endmodule
module nios_system_alu_a_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [31:0] out_port,
    input logic [31:0] readdata
);

    // First active cycle after reset release still shows the cleared state.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        $rose(reset_n) |-> (out_port == 32'h00000000 && readdata == 32'h00000000)
    );

    // Without an active write, the accumulator state holds.
    check_no_write_holds_state: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n) |=> (out_port == $past(out_port))
    );

    // Address 0 writes add writedata into the accumulator.
    check_write_add: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == ($past(out_port) + $past(writedata)))
    );

    // Address 1 writes subtract writedata from the accumulator.
    check_write_sub: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b01)) |=> (out_port == ($past(out_port) - $past(writedata)))
    );

    // Address 2 writes AND writedata with the accumulator.
    check_write_and: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b10)) |=> (out_port == ($past(out_port) & $past(writedata)))
    );

    // Address 3 writes OR writedata with the accumulator.
    check_write_or: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b11)) |=> (out_port == ($past(out_port) | $past(writedata)))
    );

    // When address[1] is low, readdata mirrors the current state.
    check_read_low_addresses_return_state: assert property (
        @(posedge clk) disable iff (!reset_n)
        !address[1] |-> (readdata == out_port)
    );

    // When address[1] is high, readdata is zero.
    check_read_high_addresses_return_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        address[1] |-> (readdata == 32'h00000000)
    );

endmodule
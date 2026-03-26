module soc_system_led_pio_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [9:0]  out_port,
    input logic [31:0] readdata
);

    // Active-low reset forces out_port to all ones.
    reset_sets_out_port_all_ones: assert property (
        @(posedge clk) !reset_n |-> (out_port == 10'b1111111111)
    );

    // A selected write to address 0 updates out_port with writedata[9:0].
    write_to_data_register_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata[9:0]))
    );

    // Without a selected write to address 0, out_port holds its value.
    no_data_register_write_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(out_port))
    );

    // Reads from address 0 return out_port in the low 10 bits.
    read_addr0_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |-> (readdata == {22'b0, out_port})
    );

    // Reads from nonzero addresses return zero.
    read_other_addresses_return_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |-> (readdata == 32'b0)
    );

    // Readdata upper bits are always zero.
    read_upper_bits_are_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (readdata[31:10] == 22'b0)
    );

endmodule